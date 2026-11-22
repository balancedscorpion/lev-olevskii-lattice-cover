module

public import AppendixA.SpectralRank
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Counting spectral sites modulo a lattice

The sites in a fixed ball that lie in one lattice coset have a uniform
cardinality bound. In the quotient group a finite set of shifts admits a
finite set whose expansion increases cardinality by at most a factor of two.
-/

public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set Metric Filter FourierTransform
open scoped Topology Pointwise FourierTransform Classical

/-- A finite set of translations in an abelian group has a nonempty finite
set whose sum with those translations has at most twice its cardinality.
The set can be chosen in any subgroup containing the translations. -/
theorem finite_translations_small_expansion {G : Type*} [AddCommGroup G] [DecidableEq G]
    (D : Finset G) (H : AddSubgroup G) (hD : (D : Set G) ⊆ H) :
    ∃ F : Finset G, F.Nonempty ∧ (F : Set G) ⊆ H ∧ (D + F).card ≤ 2 * F.card := by
  classical
  let value {n : ℕ} (q : D → Fin (n+1)) : G := ∑ i, (q i).val • i.val
  let box (n : ℕ) : Finset G := Finset.univ.image (@value n)
  have hpos (n) : (box n).Nonempty := Finset.univ_nonempty.image _
  have hmem (n) : (box n : Set G) ⊆ H := by
    rintro _ hx
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hx
    exact H.sum_mem fun i _ => H.nsmul_mem (hD i.property) _
  have hsize (n) : (box n).card ≤ (n+1)^D.card := by
    simpa [Fintype.card_fun] using (Finset.card_image_le (s := Finset.univ) (f := @value n))
  have hstep (n) : D + box n ⊆ box (n+1) := by
    intro g hg
    obtain ⟨x,hx,b,hb,rfl⟩ := Finset.mem_add.mp hg
    obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hb
    let j : D := ⟨x,hx⟩
    let q' (i : D) : Fin ((n+1)+1) :=
      ⟨(if i = j then 1 else 0) + (q i).val, by split_ifs <;> have := (q i).isLt <;> omega⟩
    refine Finset.mem_image.mpr ⟨q',Finset.mem_univ _,?_⟩
    simp [value,q',add_nsmul,Finset.sum_add_distrib,ite_smul,j]
  by_contra! h
  have hlow (n : ℕ) : 2^n ≤ (box n).card := by
    induction n with
    | zero => simpa using (hpos 0).card_pos
    | succ n ih =>
      rw [pow_succ, mul_comm]
      exact (Nat.mul_le_mul_left 2 ih).trans ((h _ (hpos n) (hmem n)).le.trans
        (Finset.card_le_card (hstep n)))
  have hlim := (tendsto_pow_const_div_const_pow_of_one_lt D.card (r := 2) (by norm_num)).eventually_lt_const
    (show (0:ℝ) < 1/2 by norm_num)
  obtain ⟨n,hn,hnpos⟩ := (hlim.and (eventually_gt_atTop 0)).exists
  have hnat : 2^(n-1) ≤ n^D.card := by
    simpa [Nat.sub_add_cancel hnpos] using (hlow (n-1)).trans (hsize (n-1))
  have hlt : (n:ℝ)^D.card < 2^(n-1) := by
    have hp : (2:ℝ)^n = 2^(n-1) * 2 := by conv_lhs => rw [← Nat.sub_add_cancel hnpos, pow_succ]
    change (n:ℝ)^D.card / 2^n < 1/2 at hn
    rw [div_lt_iff₀ (by positivity), hp] at hn
    linarith
  exact hlt.not_ge (by exact_mod_cast hnat)

private theorem ball_sites_finite {d : ℕ} (A : Set (Space d)) (hA : UniformlyDiscrete A)
    (r : ℝ) : (A ∩ closedBall 0 r).Finite := by
  obtain ⟨N,hN⟩ := uniformlyDiscrete_ball_embeddings hA r
  let e := (hN 0).some
  let S := {i : A // dist i.val 0 ≤ r}
  let : Finite S := Finite.of_injective e e.injective
  exact (finite_range (fun i : S => i.val.val)).subset fun x hx => ⟨⟨⟨x,hx.1⟩,hx.2⟩,rfl⟩

/-- In a fixed ball, any finite set of residues modulo a separated subgroup
lifts to at most a constant number of points per residue. -/
theorem quotient_window_card {d : ℕ} (K : Submodule ℤ (Space d))
    (hK : UniformlyDiscrete (K : Set (Space d))) (r : ℝ) :
    ∃ M : ℕ, ∀ F : Finset (Space d ⧸ K), ∃ E : Finset (Space d),
      (∀ x, ‖x‖ ≤ r → K.mkQ x ∈ F → x ∈ E) ∧ E.card ≤ M * F.card := by
  classical
  obtain ⟨M,hM⟩ := uniformlyDiscrete_ball_embeddings hK r
  refine ⟨M,fun F => ?_⟩
  let rep (q : Space d ⧸ K) := (K.mkQ_surjective q).choose
  have hrep (q) : K.mkQ (rep q) = q := (K.mkQ_surjective q).choose_spec
  let X (q : Space d ⧸ K) := {x : K // dist x.val (-rep q) ≤ r}
  let e (q) : X q ↪ Fin M := (hM (-rep q)).some
  let (q : Space d ⧸ K) : Fintype (X q) := Fintype.ofInjective (e q) (e q).injective
  let S (q : Space d ⧸ K) := Finset.univ.image (fun x : X q => rep q + x.val.val)
  refine ⟨F.biUnion S,fun x hx hq => Finset.mem_biUnion.mpr ⟨_,hq,?_⟩,?_⟩
  · let q := K.mkQ x
    have hk : x - rep q ∈ K := (Submodule.Quotient.eq K).mp (hrep q).symm
    have hd : dist (x - rep q) (-rep q) ≤ r := by simpa [dist_eq_norm] using hx
    exact Finset.mem_image.mpr ⟨⟨⟨_,hk⟩,hd⟩,Finset.mem_univ _,by change rep q + (x-rep q) = x; abel⟩
  · calc
      _ ≤ ∑ q ∈ F, (S q).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ F, M := Finset.sum_le_sum fun q _ =>
        Finset.card_image_le.trans (by simpa using Fintype.card_le_of_embedding (e q))
      _ = _ := by simp [mul_comm]

/-- Uniform rank estimate in terms of residues modulo the base lattice.
For each bound on the frequencies, only a finite set of spectral shifts
enters. The constant per residue is independent of that bound. -/
theorem character_rank_in_quotient_window {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (K G : Submodule ℤ (Space d)) (hK : UniformlyDiscrete (K : Set (Space d))) (hBG : B ⊆ G) :
    ∃ M : ℕ, ∀ S : ℝ, ∃ D : Finset (Space d ⧸ K), (D : Set (Space d ⧸ K)) ⊆ (G.map K.mkQ : Set (Space d ⧸ K)) ∧
      ∀ (F : Finset (Space d ⧸ K)) {ι : Type*} [Fintype ι] (u : ι → Space d),
        (∀ i, ‖u i‖ ≤ S) → (∀ i, K.mkQ (u i) ∈ F) →
        Module.finrank ℂ (Submodule.span ℂ (range (fun i (x : A) => (frequencyPhase (u i) x.val : ℂ)))) ≤
          M * (D + F).card := by
  classical
  obtain ⟨r,_,hbound⟩ := restricted_character_rank_bound hμ hA hν hB
  obtain ⟨M,hM⟩ := quotient_window_card K hK r
  refine ⟨M,fun S => ?_⟩
  let Y := (ball_sites_finite B hB (r+S)).toFinset
  let D := Y.image K.mkQ
  refine ⟨D,?_,fun F ι _ u hu hF => ?_⟩
  · intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
    exact ⟨y,hBG ((Set.Finite.mem_toFinset _).mp hy).1,rfl⟩
  · obtain ⟨E,hE,hcard⟩ := hM (D+F)
    refine (hbound u E (fun i y hy hnorm => hE _ hnorm ?_)).trans hcard
    have hy' : ‖y‖ ≤ r+S := calc
      ‖y‖ = ‖(y + u i) - u i‖ := by rw [add_sub_cancel_right]
      _ ≤ _ := (norm_sub_le ..).trans (add_le_add hnorm (hu i))
    rw [map_add]
    exact Finset.add_mem_add (Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset _).mpr
      ⟨hy,by simpa using hy'⟩)) (hF i)

end
end MeyerGeneralProblem.LevOlevskii
