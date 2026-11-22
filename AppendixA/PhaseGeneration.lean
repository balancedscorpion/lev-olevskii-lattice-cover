module

public import AppendixA.PhaseWindow
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.GroupTheory.Finiteness

/-!
# Finite generation from a separating spectral window

Stone–Weierstrass approximates each coordinate on the compact phase orbit
by polynomials in the window coordinates and their conjugates. Averaging
over suitable pairs of translations excludes a character outside the integer
span of their frequencies.
-/

public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set Filter Metric FourierTransform
open scoped Topology ComplexConjugate

private abbrev character {d : ℕ} (u t : Space d) : ℂ := (frequencyPhase u t : ℂ)

private theorem character_add {d : ℕ} (u v t : Space d) :
    character (u+v) t = character u t * character v t := by
  change (Real.fourierChar (inner ℝ t (u+v)) : ℂ) = _
  rw [inner_add_right, AddChar.map_add_eq_mul, Circle.coe_mul]
  rfl

private theorem character_neg {d : ℕ} (u t : Space d) :
    character (-u) t = conj (character u t) := by
  change (Real.fourierChar (inner ℝ t (-u)) : ℂ) = _
  rw [inner_neg_right, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

private theorem character_half_turn {d : ℕ} (u : Space d) (hu : u ≠ 0) :
    ∃ t, character u t = -1 := by
  have hpos := real_inner_self_pos.mpr hu
  refine ⟨(2 * inner ℝ u u)⁻¹ • u, ?_⟩
  change (Real.fourierChar (inner ℝ ((2 * inner ℝ u u)⁻¹ • u) u) : ℂ) = -1
  rw [real_inner_smul_left, Real.fourierChar_apply]
  have hh : 2 * Real.pi * ((2 * inner ℝ u u)⁻¹ * inner ℝ u u) = Real.pi := by
    field_simp
  rw [hh, Complex.exp_pi_mul_I]

private theorem character_sum_nonpositive {d : ℕ} {ι : Type*} (s : Finset ι)
    (u : ι → Space d) (hu : ∀ i ∈ s, u i ≠ 0) (c : ι → ℂ) :
    ∃ t, (∑ i ∈ s, c i * character (u i) t).re ≤ 0 := by
  classical
  induction s using Finset.induction generalizing c with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨v, hv⟩ := character_half_turn _ (hu i (Finset.mem_insert_self ..))
    obtain ⟨t, ht⟩ := ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))
      (fun j => c j * (1 + character (u j) v))
    by_contra! h
    have hh := add_pos (h t) (h (t+v))
    rw [← Complex.add_re, ← Finset.sum_add_distrib] at hh
    have hadd (j) : c j * character (u j) t + c j * character (u j) (t+v) =
        (c j * (1 + character (u j) v)) * character (u j) t := by
      simp only [character, AddChar.map_add_eq_mul, Circle.coe_mul]; ring
    simp_rw [hadd] at hh
    rw [Finset.sum_insert hi, hv] at hh
    simpa using (not_lt_of_ge ht) (by simpa using hh)

private abbrev Hull {d : ℕ} (B : Set (Space d)) :=
  closure (range (fun t : Space d => fun i : B => frequencyPhase i.val t))

private def orbit {d : ℕ} (B : Set (Space d)) (t : Space d) : Hull B :=
  ⟨_, subset_closure (mem_range_self t)⟩

private def coordinate {d : ℕ} {B : Set (Space d)} (i : B) : C(Hull B, ℂ) where
  toFun z := (z.val i : ℂ)
  continuous_toFun := continuous_subtype_val.comp ((continuous_apply i).comp continuous_subtype_val)

/-- A polynomial on the orbit has a finite expansion in the indicated
additive subgroup. Allowing repeated frequencies avoids choosing an ordering. -/
private def windowAlgebra {d : ℕ} (B : Set (Space d)) (G : AddSubgroup (Space d)) :
    StarSubalgebra ℂ C(Hull B, ℂ) where
  carrier := {f | ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (u : ι → G), ∀ t : Space d,
    f (orbit B t) = ∑ j, c j * character (u j).val t}
  algebraMap_mem' r := ⟨Unit, inferInstance, fun _ => r, fun _ => 0, fun t => by
    simp [character, frequencyPhase, orbit]⟩
  add_mem' := by
    rintro f g ⟨I,hI,c,u,hf⟩ ⟨J,hJ,b,v,hg⟩
    exact ⟨I ⊕ J, inferInstance, Sum.elim c b, Sum.elim u v, fun t => by
      simp [Fintype.sum_sum_type, hf, hg]⟩
  mul_mem' := by
    rintro f g ⟨I,hI,c,u,hf⟩ ⟨J,hJ,b,v,hg⟩
    refine ⟨I × J, inferInstance, fun ij => c ij.1 * b ij.2, fun ij => u ij.1 + v ij.2, fun t => ?_⟩
    simp only [ContinuousMap.mul_apply, hf, hg, Fintype.sum_prod_type, Finset.sum_mul_sum,
      AddSubgroup.coe_add, character_add, mul_comm, mul_assoc, mul_left_comm]
  star_mem' := by
    rintro f ⟨I,hI,c,u,hf⟩
    refine ⟨I,hI, fun i => conj (c i), fun i => -(u i), fun t => ?_⟩
    simp [hf, character_neg]

/-- A bounded part of the spectrum generates every spectral frequency over
the integers. The proof allows complex weights of arbitrarily small modulus. -/
theorem spectral_window_generates {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B) :
    ∃ R : ℝ, 0 < R ∧ B ⊆ AddSubgroup.closure (B ∩ closedBall 0 R) := by
  classical
  obtain ⟨R,hR,hsep⟩ := phase_window_separates hμ hA hν hB
  let G := AddSubgroup.closure (B ∩ closedBall 0 R)
  let P := windowAlgebra B G
  let : CompactSpace (Hull B) := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  have hc (i : B) (hi : ‖i.val‖ ≤ R) : coordinate i ∈ P := by
    have hg : i.val ∈ G := AddSubgroup.subset_closure ⟨i.property, by simpa using hi⟩
    exact ⟨Unit,inferInstance,fun _ => 1,fun _ => ⟨i.val,hg⟩,fun t => by simp [coordinate,orbit]⟩
  have hseparates : P.SeparatesPoints := by
    intro z w hzw
    have hdiff : ∃ i : B, ‖i.val‖ ≤ R ∧ z.val i ≠ w.val i := by
      by_contra! hs
      exact hzw (Subtype.ext (hsep z.val z.property w.val w.property hs))
    obtain ⟨i,hi,hd⟩ := hdiff
    refine ⟨coordinate i, ⟨_,hc i hi,rfl⟩, fun he => hd (Subtype.ext he)⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints P hseparates
  refine ⟨R,hR,fun x hx => ?_⟩
  by_contra hnot
  let F := coordinate (⟨x,hx⟩ : B)
  have hcl : F ∈ closure (P : Set C(Hull B,ℂ)) := by rw [← P.topologicalClosure_coe, htop]; trivial
  obtain ⟨g,hg,hclose⟩ := Metric.mem_closure_iff.mp hcl 1 one_pos
  obtain ⟨I,hI,c,u,hg⟩ := hg
  let v (j : I) := (u j).val - x
  have hne (i : I) (_ : i ∈ (Finset.univ : Finset I)) : v i ≠ 0 :=
    sub_ne_zero.mpr fun he => hnot (he ▸ (u i).property)
  obtain ⟨t, ht⟩ := character_sum_nonpositive Finset.univ v hne c
  let m := ∑ j, c j * character (v j) t
  have he (j : I) : character (u j).val t = character (v j) t * character x t := by
    rw [← character_add, sub_add_cancel]
  have hgt : g (orbit B t) = m * character x t := by
    rw [hg, Finset.sum_mul]; simp only [he, mul_assoc]
  have hm := (ContinuousMap.dist_apply_le_dist (f := F) (g := g) (orbit B t)).trans_lt hclose
  change dist (character x t) (g (orbit B t)) < 1 at hm
  rw [hgt, dist_eq_norm, ← one_sub_mul, norm_mul] at hm
  have hm' : ‖1 - m‖ < 1 := by simpa [character] using hm
  have hreal := (Complex.re_le_norm (1-m)).trans_lt hm'
  simp only [Complex.sub_re, Complex.one_re] at hreal
  change m.re ≤ 0 at ht
  linarith

private theorem spectral_group_fg {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B) :
    (AddSubgroup.closure B).FG := by
  obtain ⟨R,_,hgen⟩ := spectral_window_generates hμ hA hν hB
  obtain ⟨N,hN⟩ := uniformlyDiscrete_ball_embeddings hB R
  let e := (hN 0).some
  let S := {i : B // dist i.val 0 ≤ R}
  let : Finite S := Finite.of_injective e e.injective
  have hf : (B ∩ closedBall 0 R).Finite :=
    (finite_range (fun i : S => i.val.val)).subset fun x hx => ⟨⟨⟨x,hx.1⟩,hx.2⟩,rfl⟩
  exact (AddSubgroup.fg_iff _).mpr ⟨_, le_antisymm (AddSubgroup.closure_mono inter_subset_left)
    ((AddSubgroup.closure_le _).mpr hgen), hf⟩

/-- Both the support and the spectrum generate finitely generated additive
groups under the original hypotheses of Appendix A. -/
theorem support_and_spectrum_groups_fg {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B) :
    (AddSubgroup.closure A).FG ∧ (AddSubgroup.closure B).FG := by
  obtain ⟨hinv,hsep⟩ := inverse_atomic_expansion hν hB
  exact ⟨spectral_group_fg hinv hsep (by simpa using hμ) hA,
    spectral_group_fg hμ hA hν hB⟩

end
end MeyerGeneralProblem.LevOlevskii
