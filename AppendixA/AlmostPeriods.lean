module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Simultaneous recurrence of finitely many Fourier phases

A finite product of circles is compact, even when the frequency group has
incommensurate generators. Cover its phase image by balls and lift their
centers to obtain relatively dense simultaneous almost periods.
-/

public section

namespace MeyerGeneralProblem.LevOlevskii

open Metric Set

/-- At relatively dense translations all the characters in a finite family
are simultaneously arbitrarily close to one. No independence or periodicity
assumption on the frequencies is needed. -/
theorem relatively_dense_phase_returns {E ι : Type*} [NormedAddCommGroup E] [Fintype ι]
    (χ : ι → AddChar E Circle) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ c : E, ∃ t : E, dist c t ≤ R ∧ ∀ i, ‖(χ i t : ℂ) - 1‖ < ε := by
  classical
  let F (x : E) : ι → Circle := fun i => χ i x
  obtain ⟨S, hsub, hfin, hcover⟩ := exists_finite_cover_balls_of_isCompact_closure
    ((isClosed_closure (s := range F)).isCompact) hε
  choose lift hlift using fun z : S => hsub z.property
  let := hfin.fintype
  refine ⟨∑ z : S, ‖lift z‖, fun c => ?_⟩
  obtain ⟨y, hy⟩ := mem_iUnion.mp (hcover (mem_range_self c))
  obtain ⟨hyS, hball⟩ := mem_iUnion.mp hy
  let z : S := ⟨y, hyS⟩
  have hnear : dist (F c) (F (lift z)) < ε := by simpa [hlift] using hball
  refine ⟨c - lift z, ?_, fun i => ?_⟩
  · simpa using (Finset.single_le_sum (s := Finset.univ) (f := fun y : S => ‖lift y‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ z))
  · have hi : dist (χ i c) (χ i (lift z)) < ε := (dist_le_pi_dist (F c) (F (lift z)) i).trans_lt hnear
    change dist (χ i c : ℂ) (χ i (lift z) : ℂ) < ε at hi
    rw [dist_eq_norm] at hi
    rw [AddChar.map_sub_eq_div, Circle.coe_div]
    simpa [div_sub_one (χ i (lift z)).coe_ne_zero, norm_div] using hi

/-- An absolutely convergent Fourier series has relatively dense uniform
almost periods. The finite approximation uses the same frequencies at every
test location, so both tails in the translation estimate are uniform. -/
theorem relatively_dense_almost_periods_series {E ι : Type*} [NormedAddCommGroup E]
    (χ : ι → AddChar E Circle) (b : ι → ℂ) (hb : Summable fun i => ‖b i‖)
    {ε : ℝ} (hε : 0 < ε) :
    let F := fun (x : E) => ∑' i, b i * (χ i x : ℂ)
    ∃ R : ℝ, ∀ c, ∃ t, dist c t ≤ R ∧ ∀ x, dist (F (x + t)) (F x) < ε := by
  classical
  let term (i : ι) (x : E) := b i * (χ i x : ℂ)
  let F (x : E) := ∑' i, term i x
  have hu := tendstoUniformly_tsum (f := term) hb (fun i x => by simp [term])
  obtain ⟨S, hS⟩ := (Metric.tendstoUniformly_iff.mp hu (ε / 4) (by positivity)).exists
  let P (x : E) := ∑ i ∈ S, term i x
  let B := ∑ i ∈ S, ‖b i‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let δ := (ε / 4) / (B + 1)
  have hδ : 0 < δ := div_pos (by positivity) (by positivity)
  obtain ⟨R, hR⟩ := relatively_dense_phase_returns (fun i : S => χ i.val) hδ
  refine ⟨R, fun c => ?_⟩
  obtain ⟨t, ht, hphase⟩ := hR c
  refine ⟨t, ht, fun x => ?_⟩
  have hmid : dist (P (x + t)) (P x) ≤ B * δ := by
    rw [dist_eq_norm, show B = ∑ i ∈ S, ‖b i‖ from rfl, Finset.sum_mul]
    simp only [P, ← Finset.sum_sub_distrib]
    apply norm_sum_le_of_le
    intro i hi
    have heq : term i (x + t) - term i x = term i x * ((χ i t : ℂ) - 1) := by
      simp [term, AddChar.map_add_eq_mul, mul_sub, mul_assoc]
    rw [heq, norm_mul]
    simpa [term] using mul_le_mul_of_nonneg_left (hphase ⟨i, hi⟩).le (norm_nonneg (b i))
  have hsmall : B * δ ≤ ε / 4 := by
    calc
      _ ≤ (B + 1) * δ := by gcongr; linarith
      _ = _ := by dsimp [δ]; field_simp
  have h₁ : dist (F (x + t)) (P (x + t)) < ε / 4 := hS _
  have h₂ : dist (F x) (P x) < ε / 4 := hS _
  have htri := dist_triangle4 (F (x + t)) (P (x + t)) (P x) (F x)
  rw [dist_comm (P x) (F x)] at htri
  change dist (F (x + t)) (F x) < ε
  linarith

/-- If a localized test against an atomic measure gives a nonzero Fourier
series and can only respond within distance `r` of an atom, then the active
atoms are relatively dense. This also applies after polynomial modulation. -/
theorem relatively_dense_of_localized_series {E ι : Type*} [NormedAddCommGroup E]
    (A : Set E) (χ : ι → AddChar E Circle) (b : ι → ℂ) (hb : Summable fun i => ‖b i‖)
    (F : E → ℂ) (hF : ∀ x, F x = ∑' i, b i * (χ i x : ℂ))
    (hnonzero : ∃ p, F p ≠ 0) (r : ℝ)
    (hlocal : ∀ y, F y ≠ 0 → ∃ x ∈ A, dist y x ≤ r) :
    ∃ R : ℝ, ∀ c : E, ∃ x ∈ A, dist c x ≤ R := by
  obtain ⟨p, hp⟩ := hnonzero
  obtain ⟨R, hR⟩ := relatively_dense_almost_periods_series χ b hb (norm_pos_iff.mpr hp)
  refine ⟨R + r, fun c => ?_⟩
  obtain ⟨t, ht, hperiod⟩ := hR (c - p)
  have hclose := hperiod p
  dsimp only at hclose
  rw [← hF, ← hF] at hclose
  have hpt : F (p + t) ≠ 0 := fun h => by simp [h] at hclose
  obtain ⟨x, hx, hdist⟩ := hlocal _ hpt
  have hshift : dist c (p + t) = dist (c - p) t := by
    rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
  exact ⟨x, hx, (dist_triangle c (p + t) x).trans (add_le_add (hshift.trans_le ht) hdist)⟩

end MeyerGeneralProblem.LevOlevskii
