module

public import AppendixA.AtomicSeries
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Interpolation on separated sites

Dilation makes the absolute sum of the off-diagonal samples of a Schwartz
kernel arbitrarily small. The dilation depends only on the separation, the
kernel and the desired error.
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section
open MeasureTheory Metric Filter FourierTransform
open scoped Topology FourierTransform lp ENNReal

/-- The same dilation controls every column of every sampling matrix with
the given separation, including matrices on infinite carriers. -/
theorem separated_schwartz_offDiagonal {d : ℕ} (φ : SchwartzMap (Space d) ℂ)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ {ι : Type*} [DecidableEq ι] (u : ι → Space d)
      (_ : ∀ i j, i ≠ j → η ≤ dist (u i) (u j)) (j : ι) (t : Finset ι),
      (∑ i ∈ t with i ≠ j, ‖φ (L • (u i - u j))‖) ≤ ε := by
  classical
  let s := d + 1
  obtain ⟨C, hC⟩ := separated_inverse_weight_bound (d := d) hη s (Nat.lt_succ_self _)
  let D : ℝ := 2 ^ (s+1) * (Finset.Iic (s+1, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ
  have hD : 0 ≤ D := mul_nonneg (by positivity) (apply_nonneg _ _)
  have hφ (x : Space d) : (1 + ‖x‖) ^ (s+1) * ‖φ x‖ ≤ D := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (s+1, 0)) le_rfl le_rfl φ x
  let L := max 1 (D * C / ε / η)
  have hL : 1 ≤ L := le_max_left ..
  have hL0 : 0 ≤ L := by linarith
  have hscale : D * C ≤ ε * (1 + L * η) := by
    have hh := (div_le_iff₀ hη).mp (le_max_right 1 (D * C / ε / η))
    have hh' := (div_le_iff₀ hε).mp hh
    change D * C ≤ ε * (1 + L * η)
    change D * C ≤ L * η * ε at hh'
    linarith
  refine ⟨L, hL, ?_⟩
  intro ι inst u hsep j t
  let v (i : ι) := u i - u j
  have hoff (i : ι) (hne : i ≠ j) :
      ‖φ (L • v i)‖ ≤ (D / (1 + L * η)) * ((1 + ‖v i‖) ^ s)⁻¹ := by
    have hηi : η ≤ ‖v i‖ := by simpa [v, ← dist_eq_norm] using hsep i j hne
    have hn : ‖L • v i‖ = L * ‖v i‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hL0]
    have hi : 1 + ‖v i‖ ≤ 1 + ‖L • v i‖ := by rw [hn]; nlinarith [norm_nonneg (v i)]
    have hb : 1 + L * η ≤ 1 + ‖L • v i‖ := by rw [hn]; gcongr
    have hp : (1 + ‖v i‖)^s * (1 + L * η) ≤ (1 + ‖L • v i‖)^(s+1) := by
      exact (mul_le_mul (pow_le_pow_left₀ (by positivity) hi _) hb (by positivity) (by positivity)).trans_eq (pow_succ _ s).symm
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), le_div_iff₀ (by positivity)]
    calc
      _ = ‖φ (L • v i)‖ * ((1 + ‖v i‖)^s * (1 + L * η)) := by ring
      _ ≤ ‖φ (L • v i)‖ * (1 + ‖L • v i‖)^(s+1) := by gcongr
      _ ≤ D := by simpa [mul_comm] using hφ (L • v i)
  have hsum := hC v (fun i k hik => by simpa [v] using hsep i k hik) (t.filter (· ≠ j))
  calc
    _ ≤ ∑ i ∈ t with i ≠ j, (D / (1 + L * η)) * ((1 + ‖v i‖)^s)⁻¹ :=
      Finset.sum_le_sum fun i hi => hoff i (Finset.mem_filter.mp hi).2
    _ ≤ D / (1 + L * η) * C := by rw [← Finset.mul_sum]; gcongr
    _ ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      exact hscale

/-- Invert a sampling matrix whose off-diagonal columns have ℓ¹ norm at
most one half. The inverse sends absolutely summable data to coefficients
of norm at most twice the data norm. -/
private theorem invert_sampling_columns {ι : Type*} (P : ι → ℓ¹(ι, ℂ))
    (hP : ∀ j, ‖P j‖ ≤ 1 / 2) (b : ℓ¹(ι, ℂ)) :
    ∃ c : ℓ¹(ι, ℂ), ‖c‖ ≤ 2 * ‖b‖ ∧ HasSum (fun j => c j • P j) (b - c) := by
  let E (c : ℓ¹(ι, ℂ)) := ∑' j, c j • P j
  have hcn (c : ℓ¹(ι, ℂ)) : Summable fun j => ‖c j‖ := by simpa using c.2.summable
  have hdom (c : ℓ¹(ι, ℂ)) (j : ι) : ‖c j • P j‖ ≤ ‖c j‖ * (1 / 2) := by
    rw [norm_smul]; gcongr; exact hP j
  have habs (c : ℓ¹(ι, ℂ)) : Summable fun j => ‖c j • P j‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hdom c) ((hcn c).mul_right _)
  have hs (c : ℓ¹(ι, ℂ)) : Summable fun j => c j • P j :=
    Summable.of_norm_bounded ((hcn c).mul_right (1 / 2)) (hdom c)
  have hbound (c : ℓ¹(ι, ℂ)) : ‖E c‖ ≤ (1 / 2) * ‖c‖ := by
    calc
      _ ≤ ∑' j, ‖c j • P j‖ := norm_tsum_le_tsum_norm (habs c)
      _ ≤ ∑' j, ‖c j‖ * (1 / 2) :=
        (habs c).tsum_le_tsum (hdom c) ((hcn c).mul_right _)
      _ = _ := by rw [tsum_mul_right, lp.norm_eq_tsum_rpow (f := c) (by norm_num)]; simp [mul_comm]
  let F (c : ℓ¹(ι, ℂ)) := b - E c
  have hF : ContractingWith (1 / 2) F := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun c e => ?_⟩
    rw [dist_eq_norm, dist_eq_norm]
    have hd : E c - E e = E (c - e) := by
      unfold E
      rw [← (hs c).tsum_sub (hs e)]
      exact tsum_congr fun j => (sub_smul (c j) (e j) (P j)).symm
    change ‖(b - E c) - (b - E e)‖ ≤ _
    rw [sub_sub_sub_cancel_left, ← neg_sub, norm_neg, hd]
    simpa using hbound (c - e)
  let c := hF.fixedPoint F
  have heq : b - E c = c := hF.fixedPoint_isFixedPt
  refine ⟨c, ?_, ?_⟩
  · have hh := norm_sub_le b (E c)
    rw [heq] at hh
    linarith [hbound c]
  · have hc : E c = b - c := calc
      E c = b - (b - E c) := by abel
      _ = b - c := congrArg (b - ·) heq
    rw [← hc]
    exact (hs c).hasSum

/-- Interpolate any ℓ¹ data using translates of one dilated Schwartz kernel
with value one at zero. The coefficient bound and dilation are uniform over all
sets with the specified separation. -/
theorem separated_schwartz_interpolation {d : ℕ} (φ : SchwartzMap (Space d) ℂ)
    (hφ : φ 0 = 1) {η : ℝ} (hη : 0 < η) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ {ι : Type*} (u : ι → Space d)
      (_ : ∀ i j, i ≠ j → η ≤ dist (u i) (u j)) (b : ℓ¹(ι, ℂ)),
      ∃ c : ℓ¹(ι, ℂ), ‖c‖ ≤ 2 * ‖b‖ ∧
        ∀ i, HasSum (fun j => c j * φ (L • (u i - u j))) (b i) := by
  classical
  obtain ⟨L, hL, hoff⟩ := separated_schwartz_offDiagonal φ hη (show 0 < (1:ℝ)/2 by norm_num)
  refine ⟨L, hL, ?_⟩
  intro ι u hsep b
  let K (j i : ι) : ℂ := if i = j then 0 else φ (L • (u i - u j))
  have hcol (j : ι) (t : Finset ι) : ∑ i ∈ t, ‖K j i‖ ≤ 1 / 2 := by
    simpa [K, apply_ite, Finset.sum_filter, ite_not] using hoff u hsep j t
  let P (j : ι) : ℓ¹(ι, ℂ) := ⟨K j, (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mpr (by
    simpa using summable_of_sum_le (fun i => norm_nonneg (K j i)) (hcol j))⟩
  have hP (j : ι) : ‖P j‖ ≤ 1 / 2 :=
    lp.norm_le_of_forall_sum_le (by norm_num) (by norm_num) (by simpa [P] using hcol j)
  obtain ⟨c, hc, hs⟩ := invert_sampling_columns P hP b
  refine ⟨c, hc, fun i => ?_⟩
  have he := (lp.evalCLM ℂ (fun _ : ι => ℂ) 1 i).hasSum hs
  change HasSum (fun j => c j * K j i) (b i - c i) at he
  have hi := hasSum_ite_eq i (c i)
  convert he.add hi using 1
  · ext j
    by_cases hij : i = j
    · subst j; simp [K, hφ]
    · simp [K, hij, Ne.symm hij]
  · abel

end
end MeyerGeneralProblem.LevOlevskii
