module

public import AppendixA.CombWeights

/-!
# Finite orbits of one lattice modulo another

When a lattice has finite image modulo a second lattice, adding it to a
coset of the second lattice leaves a closed finite union of cosets. Its
image modulo the first lattice is finite as well, by reduction to a bounded
fundamental domain.
-/

@[expose] public section

namespace MeyerGeneralProblem.LevOlevskii

noncomputable section

open Set Metric Matrix Module
open scoped Matrix Classical

/-- Nonnegative integer coordinates in a lattice basis. -/
def natLatticePoint {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℕ) : Space d :=
  ∑ i, q i • WithLp.toLp 2 (P.col i)

theorem natLatticePoint_add {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (q v : Fin d → ℕ) :
    natLatticePoint P (q + v) = natLatticePoint P q + natLatticePoint P v := by
  simp [natLatticePoint, add_nsmul, Finset.sum_add_distrib]

theorem natLatticePoint_mem {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ) (q : Fin d → ℕ) :
    natLatticePoint P q ∈ matrixLattice P :=
  Submodule.sum_mem _ fun i _ => (matrixLattice P).toAddSubmonoid.nsmul_mem (Submodule.subset_span (mem_range_self i)) (q i)

theorem boxFrequency_eq_natLatticePoint {d N : ℕ} (T : Matrix (Fin d) (Fin d) ℝ)
    (q : Fin d → Fin (N+1)) : boxFrequency T q = natLatticePoint (dualMatrix T) (fun i => (q i).val) := rfl

theorem infinite_lattice_orbit_shifts {d : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (K : Submodule ℤ (Space d)) (hinf : (K.mkQ '' (matrixLattice P : Set (Space d))).Infinite) (m : ℕ) :
    ∃ v : Fin m → Fin d → ℕ, Function.Injective (fun j => K.mkQ (natLatticePoint P (v j))) := by
  let S := range (fun q => K.mkQ (natLatticePoint P q))
  have hS : S.Infinite := by
    intro hfin
    apply hinf
    apply (hfin.image2 (· - ·) hfin).subset
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    let v (i : Fin d) := (z i).toNat
    let w (i : Fin d) := (-z i).toNat
    refine ⟨_, ⟨v, rfl⟩, _, ⟨w, rfl⟩, ?_⟩
    change K.mkQ _ - K.mkQ _ = K.mkQ x
    rw [← map_sub, ← hz, natLatticePoint, natLatticePoint, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have heq : (v i : ℤ) - (w i : ℤ) = z i := by dsimp [v, w]; omega
    rw [← heq, sub_zsmul, natCast_zsmul, natCast_zsmul, sub_eq_add_neg]
  let := hS.to_subtype
  let e : Fin m ↪ S := Fin.valEmbedding.trans (Infinite.natEmbedding S)
  choose v hv using fun j => (e j).property
  refine ⟨v, fun i j hij => e.injective (Subtype.ext ?_)⟩
  simpa only [← hv] using hij

theorem matrixLattice_closed {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) (hT : T.det ≠ 0) :
    IsClosed (matrixLattice T : Set (Space d)) := by
  obtain ⟨η, hη, hs⟩ := latticeCoset_uniformlyDiscrete 0 T hT
  have heq : range (latticeSite 0 T) = (matrixLattice T : Set (Space d)) := by
    ext x
    simp only [mem_latticeCoset_iff, sub_zero, SetLike.mem_coe]
  exact heq ▸ Metric.isClosed_of_pairwise_le_dist hη hs

/-- The coset enlarged by every translation in the averaging lattice. -/
def enlargedCoset {d : ℕ} (H K : Submodule ℤ (Space d)) (p : Space d) : Set (Space d) :=
  {x | ∃ h ∈ H, x - p - h ∈ K}

theorem enlargedCoset_add {d : ℕ} {H K : Submodule ℤ (Space d)} {p x u : Space d}
    (hx : x ∈ enlargedCoset H K p) (hu : u ∈ H) : x + u ∈ enlargedCoset H K p := by
  obtain ⟨v, hv, h⟩ := hx
  exact ⟨v + u, H.add_mem hv hu, by rwa [show x + u - p - (v + u) = x - p - v by abel]⟩

private theorem matrix_fundamental_region {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ) (hT : T.det ≠ 0) :
    ∃ U : Set (Space d), Bornology.IsBounded U ∧ ∀ x : Space d,
      ∃ h ∈ matrixLattice T, x - h ∈ U := by
  let f (i : Fin d) : Space d := WithLp.toLp 2 (T.col i)
  have hli : LinearIndependent ℝ f :=
    ((WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).symm.toLinearMap.linearIndependent_iff (by simp)).mpr
      (Matrix.linearIndependent_cols_iff_isUnit.mpr (T.isUnit_iff_isUnit_det.mpr (isUnit_iff_ne_zero.mpr hT)))
  let b := basisOfLinearIndependentOfCardEqFinrank' f hli (by simp)
  have hb : ⇑b = f := Basis.coe_mk ..
  refine ⟨ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_isBounded b, fun x => ?_⟩
  refine ⟨ZSpan.floor b x, ?_, ZSpan.fract_mem_fundamentalDomain b x⟩
  change _ ∈ Submodule.span ℤ (range f)
  rw [← hb]
  exact (ZSpan.floor b x).property

theorem finite_lattice_orbit {d : ℕ} (P T : Matrix (Fin d) (Fin d) ℝ)
    (hP : P.det ≠ 0) (hT : T.det ≠ 0) (p : Space d)
    (hfin : ((matrixLattice T).mkQ '' (matrixLattice P : Set (Space d))).Finite) :
    let H := matrixLattice P
    let U := enlargedCoset H (matrixLattice T) p
    IsClosed U ∧ (H.mkQ '' U).Finite := by
  let H := matrixLattice P
  let K := matrixLattice T
  let S := K.mkQ '' (H : Set (Space d))
  let := hfin.fintype
  choose pick hp hq using fun i : S => i.property
  let D (i : S) := range (latticeSite (p + pick i) T)
  have heq : enlargedCoset H K p = ⋃ i, D i := by
    ext x
    constructor
    · rintro ⟨h, hh, hx⟩
      let i : S := ⟨K.mkQ h, h, hh, rfl⟩
      have hdiff : h - pick i ∈ K := (Submodule.Quotient.eq K).mp (hq i).symm
      refine mem_iUnion.mpr ⟨i, (mem_latticeCoset_iff ..).mpr ?_⟩
      convert K.add_mem hx hdiff using 1
      abel
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      refine ⟨pick i, hp i, ?_⟩
      simpa only [sub_add_eq_sub_sub] using (mem_latticeCoset_iff ..).mp hi
  have hclosed (i : S) : IsClosed (D i) := by
    obtain ⟨η, hη, hs⟩ := latticeCoset_uniformlyDiscrete (p + pick i) T hT
    exact Metric.isClosed_of_pairwise_le_dist hη hs
  refine ⟨heq ▸ isClosed_iUnion_of_finite hclosed, ?_⟩
  obtain ⟨V, hV, hrep⟩ := matrix_fundamental_region P hP
  have hfinite (i : S) : (V ∩ D i).Finite := by
    obtain ⟨η, hη, hs⟩ := latticeCoset_uniformlyDiscrete (p + pick i) T hT
    have hdisc : IsDiscrete (D i) := by
      apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
      intro x hx
      refine ⟨ball x η, isOpen_ball, Set.ext fun y => ?_⟩
      constructor
      · rintro ⟨hy, hyD⟩
        by_contra hne
        exact hy.not_ge (hs hyD hx hne)
      · rintro rfl
        exact ⟨mem_ball_self hη, hx⟩
    exact Metric.finite_isBounded_inter_isClosed hdisc hV (hclosed i)
  apply ((Set.finite_iUnion hfinite).image H.mkQ).subset
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨h, hh, hVx⟩ := hrep x
  have hmem := enlargedCoset_add hx (H.neg_mem hh)
  rw [← sub_eq_add_neg, heq] at hmem
  obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
  refine ⟨x - h, mem_iUnion.mpr ⟨i, hVx, hi⟩, ?_⟩
  rw [map_sub, show H.mkQ h = 0 from (Submodule.Quotient.mk_eq_zero H).mpr hh, sub_zero]

end
end MeyerGeneralProblem.LevOlevskii
