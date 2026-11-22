module

public import AppendixA.CompactApproximation
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# Absolute convergence on separated supports

Equal-radius balls around distinct sites are disjoint. Integration of an
inverse polynomial over those balls bounds all finite partial sums of its
values on the sites, with an exponent depending only on the dimension.
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

open MeasureTheory Metric Filter
open scoped Topology
noncomputable section

/-- An inverse polynomial of degree greater than the ambient dimension
is summable on any uniformly discrete carrier. -/
theorem summable_inverse_weight {d : ℕ} {A : Set (Space d)}
    (hA : UniformlyDiscrete A) (s : ℕ) (hs : d < s) :
    Summable (fun x : A => ((1 + ‖(x : Space d)‖) ^ s)⁻¹) := by
  classical
  obtain ⟨η, hη, hsep⟩ := hA
  let r := η / 2
  have hr : 0 < r := half_pos hη
  let B (x : A) := ball (x : Space d) r
  let w (y : Space d) := ((1 + ‖y‖) ^ s)⁻¹
  let f (y : Space d) := (1 + r) ^ s * w y
  have hw : Integrable w := by
    have hdim : (Module.finrank ℝ (Space d) : ℝ) < (s : ℝ) := by
      simpa using (show (d : ℝ) < s by exact_mod_cast hs)
    simpa [w, Real.rpow_neg (by positivity : ∀ x : Space d, 0 ≤ 1 + ‖x‖)] using
      (integrable_one_add_norm (μ := volume) hdim)
  have hf : Integrable f := hw.const_mul _
  let V := volume.real (ball (0 : Space d) r)
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume _ hr).ne' measure_ball_lt_top.ne
  have hlocal (x : A) (y) (hy : y ∈ B x) : w x ≤ f y := by
    have hnorm := norm_le_norm_add_norm_sub (x : Space d) y
    rw [norm_sub_rev] at hnorm
    have hdist : ‖y - (x : Space d)‖ < r := by simpa [B, dist_eq_norm] using hy
    have hbase : 1 + ‖y‖ ≤ (1 + r) * (1 + ‖(x : Space d)‖) := by
      nlinarith [mul_nonneg hr.le (norm_nonneg (x : Space d))]
    have hpow := pow_le_pow_left₀ (by positivity) hbase s
    rw [mul_pow] at hpow
    change _⁻¹ ≤ _ * _⁻¹
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    rwa [inv_mul_eq_div, div_le_iff₀ (by positivity)]
  have hxbound (x : A) : w x * V ≤ ∫ y in B x, f y := by
    have hconst : IntegrableOn (fun _ : Space d => w x) (B x) :=
      integrableOn_const measure_ball_lt_top.ne
    have h := setIntegral_mono_on hconst hf.integrableOn measurableSet_ball (hlocal x)
    simpa [B, setIntegral_const, Measure.addHaar_real_ball_center, V, mul_comm] using h
  apply summable_of_sum_le (c := (∫ y, f y) / V) (fun _ => by positivity)
  intro t
  apply (le_div_iff₀ hV).mpr
  rw [Finset.sum_mul]
  refine (Finset.sum_le_sum fun x _ => hxbound x).trans ?_
  rw [← integral_biUnion_finset t (s := B) (fun _ _ => measurableSet_ball) _ (fun _ _ => hf.integrableOn)]
  · apply setIntegral_le_integral hf (ae_of_all _ fun y => ?_)
    dsimp [f, w]; positivity
  · intro x _ y _ hne
    refine Set.disjoint_left.mpr fun z hx hy => ?_
    have hxy := hsep x.property y.property (fun h => hne (Subtype.ext h))
    have htri := dist_triangle (x : Space d) z y
    have h1 : dist (x : Space d) z < η / 2 := (mem_ball'.mp hx)
    have h2 : dist z (y : Space d) < η / 2 := hy
    linarith

/-- The actual atomic expansion converges absolutely on every Schwartz test,
using a polynomial bound deduced from the distribution itself. -/
theorem summable_atomic_schwartz {d : ℕ} {A : Set (Space d)} {a : A → ℂ}
    {μ : TemperedDistribution (Space d) ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (φ : SchwartzMap (Space d) ℂ) : Summable (fun x : A => ‖a x * φ x‖) := by
  obtain ⟨N, C, hC, ha⟩ := atomic_coefficients_polynomial_growth hμ hA
  let s := d + 1
  let k := N + s
  let D : ℝ := 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2) φ
  have hφ (x : Space d) : (1 + ‖x‖) ^ k * ‖φ x‖ ≤ D := by
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl φ x
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    ((summable_inverse_weight hA s (Nat.lt_succ_self _)).mul_left (C * D))
  intro x
  rw [norm_mul, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc
    _ ≤ (C * (1 + ‖(x : Space d)‖) ^ N * ‖φ x‖) * (1 + ‖(x : Space d)‖) ^ s := by
      gcongr; exact ha x
    _ = C * ((1 + ‖(x : Space d)‖) ^ k * ‖φ x‖) := by dsimp [k]; rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hφ x) hC

/-- The local atomic identity extends to all Schwartz tests. Uniform
separation and continuity of the given distribution suffice on this side. -/
theorem atomicExpansion_of_locallyAtomic_of_uniformlyDiscrete {d : ℕ}
    {A : Set (Space d)} {a : A → ℂ} {μ : TemperedDistribution (Space d) ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A) :
    HasAtomicExpansion μ A a := by
  refine ⟨hμ.1, fun φ => ?_⟩
  obtain ⟨ψ, hc, hbound, hevent, hlim⟩ := exists_bounded_compact_schwartz_approximation φ
  have hsum := summable_atomic_schwartz hμ hA φ
  have hts := tendsto_tsum_of_dominated_convergence
    (f := fun (n : ℕ) (x : A) => a x * ψ n x) (g := fun x => a x * φ x) hsum
    (fun x => tendsto_const_nhds.congr' ((hevent x).mono (fun _ h => congrArg (a x * ·) h.symm)))
    (Eventually.of_forall (fun n x => by
      rw [norm_mul, norm_mul]; gcongr; exact hbound n x))
  have heq (n : ℕ) : (∑' x : A, a x * ψ n x) = μ (ψ n) := (hμ.2 _ (hc n)).tsum_eq
  have hval := tendsto_nhds_unique hts ((μ.continuous.tendsto φ).comp hlim |>.congr (fun n => (heq n).symm))
  exact hval ▸ hsum.of_norm.hasSum

end
end MeyerGeneralProblem.LevOlevskii
