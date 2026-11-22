module

public import AppendixA.AtomicGrowth
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Compact approximation in the Schwartz topology

Cut off a Schwartz test with one smooth unit bump dilated by growing radii.
All derivatives of the multipliers are bounded uniformly in the radius. On
the exterior, one extra Schwartz weight then forces the error to zero.
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

open Filter Metric
open scoped Topology ContDiff
noncomputable section

private def dilation (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) : E →L[ℝ] E :=
  ((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ E

private theorem norm_dilation_le_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) : ‖dilation E n‖ ≤ 1 := by
  rw [dilation, norm_smul, Real.norm_of_nonneg (by positivity)]
  exact (mul_le_of_le_one_right (by positivity) ContinuousLinearMap.norm_id_le).trans
    (inv_le_one_of_one_le₀ (le_add_of_nonneg_left (by positivity)))

private def unitBump (d : ℕ) : ContDiffBump (0 : Space d) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private def cutoff (d n : ℕ) : Space d → ℝ := unitBump d ∘ dilation (Space d) n

private theorem cutoff_smooth (d n : ℕ) : ContDiff ℝ ∞ (cutoff d n) :=
  (unitBump d).contDiff.comp (dilation (Space d) n).contDiff

private theorem cutoff_compact (d n : ℕ) : HasCompactSupport (cutoff d n) :=
  (unitBump d).hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero (((n : ℝ) + 1)⁻¹) (by positivity))

private theorem cutoff_one {d n : ℕ} {x : Space d} (hx : ‖x‖ ≤ (n : ℝ) + 1) :
    cutoff d n x = 1 := by
  apply (unitBump d).one_of_mem_closedBall
  change dist ((((n : ℝ) + 1)⁻¹) • x) 0 ≤ 1
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity), inv_mul_eq_div,
    div_le_one (by positivity)]
  exact hx

private theorem cutoff_derivative_bound (d i : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n x, ‖iteratedFDeriv ℝ i (cutoff d n) x‖ ≤ B := by
  let b := unitBump d
  let φ := b.hasCompactSupport.toSchwartzMap b.contDiff
  refine ⟨SchwartzMap.seminorm ℝ 0 i φ, apply_nonneg _ _, fun n x => ?_⟩
  let L := dilation (Space d) n
  rw [cutoff, L.iteratedFDeriv_comp_right (b.contDiff : ContDiff ℝ ∞ b) x (by simp)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_fin]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (norm_dilation_le_one n))).trans
    (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ φ i (L x))

private def cutTest {d : ℕ} (φ : SchwartzMap (Space d) ℂ) (n : ℕ) :
    SchwartzMap (Space d) ℂ :=
  ((cutoff_compact d n).smul_right (f' := (φ : Space d → ℂ))).toSchwartzMap
    ((cutoff_smooth d n).smul (φ.smooth _))

private theorem cutTest_seminorm_bounded {d : ℕ} (φ : SchwartzMap (Space d) ℂ) (k l : ℕ) :
    ∃ C : ℝ, ∀ n, SchwartzMap.seminorm ℂ k l (cutTest φ n - φ) ≤ C := by
  choose B hB hbound using cutoff_derivative_bound d
  let C := ∑ i ∈ Finset.range (l+1),
    (l.choose i : ℝ) * B i * SchwartzMap.seminorm ℂ k (l-i) φ
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (by positivity) (hB i)) (apply_nonneg _ _)
  refine ⟨C + SchwartzMap.seminorm ℂ k l φ, fun n => ?_⟩
  rw [sub_eq_add_neg]
  refine (map_add_le_add (SchwartzMap.seminorm ℂ k l) _ _).trans ?_
  rw [map_neg_eq_map]
  apply add_le_add_left
  apply SchwartzMap.seminorm_le_bound ℂ k l _ hC
  intro x
  have hp := norm_iteratedFDeriv_smul_le (cutoff_smooth d n) (φ.smooth _) x (n := l) (by simp)
  refine (mul_le_mul_of_nonneg_left hp (pow_nonneg (norm_nonneg _) k)).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ = (l.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutoff d n) x‖ *
        (‖x‖ ^ k * ‖iteratedFDeriv ℝ (l-i) (⇑φ) x‖) := by ring
    _ ≤ _ := by
      gcongr <;> first | exact hbound i n x | exact SchwartzMap.le_seminorm ℂ k (l-i) φ x | exact mul_nonneg (by positivity) (hB i)

/-- A Schwartz test is the limit, in every Schwartz seminorm, of compact
tests. Pointwise they are eventually equal to it and bounded by its norm. -/
theorem exists_bounded_compact_schwartz_approximation {d : ℕ} (φ : SchwartzMap (Space d) ℂ) :
    ∃ ψ : ℕ → SchwartzMap (Space d) ℂ,
      (∀ n, HasCompactSupport (ψ n : Space d → ℂ)) ∧
      (∀ n x, ‖ψ n x‖ ≤ ‖φ x‖) ∧ (∀ x, ∀ᶠ n : ℕ in atTop, ψ n x = φ x) ∧
      Tendsto ψ atTop (𝓝 φ) := by
  refine ⟨cutTest φ, (fun n => (cutoff_compact d n).smul_right), ?_, ?_, ?_⟩
  · intro n x
    change ‖cutoff d n x • φ x‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ cutoff d n x from (unitBump d).nonneg)]
    exact mul_le_of_le_one_left (norm_nonneg _) (unitBump d).le_one
  · intro x
    obtain ⟨m, hm⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop m] with n hn
    change cutoff d n x • φ x = φ x
    rw [cutoff_one (by linarith [show (m : ℝ) ≤ n by exact_mod_cast hn]), one_smul]
  · apply ((schwartz_withSeminorms ℂ (Space d) ℂ).tendsto_nhds_atTop _ _).mpr
    rintro ⟨k, l⟩ ε hε
    obtain ⟨C, hC⟩ := cutTest_seminorm_bounded φ (k + 1) l
    obtain ⟨m, hm⟩ := exists_nat_gt (C / (ε / 2))
    refine ⟨m, fun n hn => ?_⟩
    apply lt_of_le_of_lt _ (half_lt_self hε)
    apply SchwartzMap.seminorm_le_bound ℂ k l _ (half_pos hε).le
    intro x
    by_cases hx : ‖x‖ < (n : ℝ) + 1
    · have heq : (⇑(cutTest φ n - φ)) =ᶠ[𝓝 x] 0 := by
        filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hx] with y hy
        change cutoff d n y • φ y - φ y = 0
        rw [cutoff_one hy.le, one_smul, sub_self]
      rw [(heq.iteratedFDeriv (𝕜 := ℝ) l).self_of_nhds]
      simp [half_pos hε |>.le]
    · have hlarge : C < ‖x‖ * (ε / 2) :=
        ((div_lt_iff₀ (half_pos hε)).mp hm).trans_le (by
          gcongr; linarith [show (m : ℝ) ≤ n by exact_mod_cast hn, le_of_not_gt hx])
      have hle := (SchwartzMap.le_seminorm ℂ (k+1) l (cutTest φ n - φ) x).trans (hC n)
      apply le_of_lt
      apply lt_of_mul_lt_mul_left (a := ‖x‖) _ (norm_nonneg _)
      calc
        _ = ‖x‖ ^ (k+1) * ‖iteratedFDeriv ℝ l (⇑(cutTest φ n - φ)) x‖ := by rw [pow_succ]; ring
        _ < _ := hle.trans_lt hlarge

end
end MeyerGeneralProblem.LevOlevskii
