module

public import AppendixA.LatticeOrbits

/-!
# Counting near hits in dual-lattice boxes

For an infinite orbit, choose arbitrarily many distinct shifts modulo the
spectral lattice. At sufficiently small test radii the shifted copies of
the set of hits are disjoint. They all fit in a box enlarged by a fixed
number of layers, independent of the original box size.
-/

@[expose] public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open Set Filter Metric
open scoped Topology Classical

/-- Box indices whose translated spectral coset meets the test ball. -/
def boxHits {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (K : Submodule ℤ (Space d))
    (p x : Space d) (r : ℝ) (N : ℕ) : Finset (Fin d → Fin (N+1)) :=
  Finset.univ.filter fun q => ∃ y : Space d, y - p ∈ K ∧
    dist (y + natLatticePoint P (fun i => (q i).val)) x < r

private theorem separated_shifts {d m : ℕ} (K : Submodule ℤ (Space d)) (hK : IsClosed (K : Set (Space d)))
    (s : Fin m → Space d) (hs : Function.Injective (fun i => K.mkQ (s i))) :
    ∀ᶠ n in atTop, ∀ i j, i ≠ j → ∀ k ∈ K, 2 * atomRadius n ≤ dist k (s i - s j) := by
  apply eventually_all.mpr
  intro i
  apply eventually_all.mpr
  intro j
  by_cases hij : i = j
  · exact .of_forall fun _ hn => (hn hij).elim
  have hout : s i - s j ∉ K := fun h => hij (hs ((Submodule.Quotient.eq K).mpr h))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl _ hout
  have hlim : Tendsto (fun n => 2 * atomRadius n) atTop (𝓝 0) := by simpa using atomRadius_tendsto.const_mul 2
  filter_upwards [hlim.eventually_lt_const hr] with n hn
  intro _ k hk
  by_contra! h
  exact hball (mem_ball.mpr (h.trans hn)) hk

/-- Each of `m` translated copies fits disjointly into the enlarged box.
The estimate is uniform in the center and the spectral translate. -/
theorem infinite_orbit_box_packing {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (K : Submodule ℤ (Space d)) (hK : IsClosed (K : Set (Space d)))
    (hinf : (K.mkQ '' (matrixLattice P : Set (Space d))).Infinite) (m : ℕ) :
    ∃ C : ℕ, ∀ᶠ n in atTop, ∀ (p x : Space d) (N : ℕ),
      m * (boxHits P K p x (atomRadius n) N).card ≤ (N + C + 1)^d := by
  obtain ⟨v, hv⟩ := infinite_lattice_orbit_shifts P K hinf m
  let s (j : Fin m) := natLatticePoint P (v j)
  let C := ∑ j, ∑ i, v j i
  have hC (j i) : v j i ≤ C := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
    (Finset.single_le_sum (f := fun k => ∑ l, v k l) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  refine ⟨C, ?_⟩
  filter_upwards [separated_shifts K hK s hv] with n hn
  intro p x N
  let Q := boxHits P K p x (atomRadius n) N
  let u (q : Q) (i : Fin d) := (q.val i).val
  let encode (a : Fin m × Q) (i : Fin d) : Fin (N + C + 1) :=
    ⟨u a.2 i + v a.1 i, by have := (a.2.val i).isLt; have := hC a.1 i; dsimp [u]; omega⟩
  have hinj : Function.Injective encode := by
    rintro ⟨i,q⟩ ⟨j,q'⟩ h
    have heq (l) := congrArg Fin.val (congrFun h l)
    have hsum : u q + v i = u q' + v j := funext heq
    have hid : i = j := by
      by_contra hij
      obtain ⟨y, hy, hnear⟩ := (Finset.mem_filter.mp q.property).2
      obtain ⟨y', hy', hnear'⟩ := (Finset.mem_filter.mp q'.property).2
      have hk : y - y' ∈ K := by simpa only [sub_sub_sub_cancel_right] using K.sub_mem hy hy'
      have hfreq := congrArg (natLatticePoint P) hsum
      simp only [natLatticePoint_add] at hfreq
      change natLatticePoint P (u q) + s i = natLatticePoint P (u q') + s j at hfreq
      have hdist : dist (y - y') (s i - s j) =
          dist (y + natLatticePoint P (u q)) (y' + natLatticePoint P (u q')) := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        linear_combination (norm := abel) -hfreq
      have hsep := hn i j hij _ hk
      rw [hdist] at hsep
      have htri := dist_triangle (y + natLatticePoint P (u q)) x (y' + natLatticePoint P (u q'))
      change dist (y + natLatticePoint P (u q)) x < _ at hnear
      change dist (y' + natLatticePoint P (u q')) x < _ at hnear'
      rw [dist_comm x] at htri
      linarith
    subst j
    congr 1
    exact Subtype.ext (funext fun l => Fin.ext (Nat.add_right_cancel (heq l)))
  simpa [Q] using Fintype.card_le_of_injective encode hinj

/-- Outside the enlarged cosets with finite orbit, a finite cover has
arbitrarily small asymptotic proportions of hits. -/
theorem cover_box_packing {d k : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (hP : P.det ≠ 0)
    (T : Fin k → Matrix (Fin d) (Fin d) ℝ) (hT : ∀ j, (T j).det ≠ 0)
    (p : Fin k → Space d) (x : Space d)
    (hx : ∀ j, ((matrixLattice (T j)).mkQ '' (matrixLattice P : Set (Space d))).Finite →
      x ∉ enlargedCoset (matrixLattice P) (matrixLattice (T j)) (p j)) (m : ℕ) :
    ∃ C : ℕ, ∀ᶠ n in atTop, ∀ N : ℕ,
      m * (Finset.univ.biUnion fun j => boxHits P (matrixLattice (T j)) (p j) x (atomRadius n) N).card ≤
        k * (N + C + 1)^d := by
  let Q (j : Fin k) (n N : ℕ) := boxHits P (matrixLattice (T j)) (p j) x (atomRadius n) N
  have hrow (j : Fin k) : ∃ C : ℕ, ∀ᶠ n in atTop, ∀ N, m * (Q j n N).card ≤ (N + C + 1)^d := by
    by_cases hf : ((matrixLattice (T j)).mkQ '' (matrixLattice P : Set (Space d))).Finite
    · obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
        (finite_lattice_orbit P (T j) hP (hT j) (p j) hf).1.isOpen_compl x (hx j hf)
      refine ⟨0, ?_⟩
      filter_upwards [atomRadius_tendsto.eventually_lt_const hr] with n hn
      intro N
      have hzero : Q j n N = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro q hq
        obtain ⟨y, hy, hdist⟩ := (Finset.mem_filter.mp hq).2
        apply hball (Metric.mem_ball.mpr (hdist.trans hn))
        apply enlargedCoset_add (H := matrixLattice P) (K := matrixLattice (T j)) (p := p j) (x := y) _ (natLatticePoint_mem P (fun i => (q i).val))
        exact ⟨0, (matrixLattice P).zero_mem, by simpa using hy⟩
      simp [hzero]
    · obtain ⟨C, hC⟩ := infinite_orbit_box_packing P _ (matrixLattice_closed _ (hT j)) hf m
      exact ⟨C, hC.mono fun _ h N => h (p j) x N⟩
  choose C hC using hrow
  refine ⟨∑ j, C j, ?_⟩
  filter_upwards [eventually_all.mpr hC] with n hn
  intro N
  change m * (Finset.univ.biUnion (fun j => Q j n N)).card ≤ _
  calc
    _ ≤ m * ∑ j, (Q j n N).card := Nat.mul_le_mul_left _ Finset.card_biUnion_le
    _ = ∑ j, m * (Q j n N).card := Finset.mul_sum ..
    _ ≤ ∑ _ : Fin k, (N + (∑ j, C j) + 1)^d := by
      apply Finset.sum_le_sum
      intro j _
      apply (hn j N).trans
      gcongr
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ = _ := by simp
end
end MeyerGeneralProblem.LevOlevskii
