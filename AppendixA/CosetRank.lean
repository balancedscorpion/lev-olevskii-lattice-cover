module

public import AppendixA.CosetCharacters
public import AppendixA.SpectralBasis

/-!
# Spanning algebraic cosets are contained in lattices

A nonspanning integral dual leaves room for arbitrarily many separated
translates in a real direction. Finite sets in the quotient by a base
lattice supply more independent characters than the spectral window permits.
-/

public section
namespace MeyerGeneralProblem.LevOlevskii
noncomputable section
open Set Matrix Metric FourierTransform Submodule
open scoped Matrix Classical Pointwise FourierTransform

private theorem base_lattice {d : ℕ} (G : Submodule ℤ (Space d))
    (hG : span ℝ (G : Set (Space d)) = ⊤) :
    ∃ K : Submodule ℤ (Space d), K ≤ G ∧ span ℝ (K : Set (Space d)) = ⊤ ∧
      UniformlyDiscrete (K : Set (Space d)) ∧ ∃ r : ℝ, 0 ≤ r ∧
      ∀ q ∈ G.map K.mkQ, ∃ v ∈ G, K.mkQ v = q ∧ ‖v‖ ≤ r := by
  have hb := exists_fun_fin_finrank_span_eq ℝ (G : Set (Space d))
  rw [hG,finrank_top,finrank_euclideanSpace_fin] at hb
  obtain ⟨v,hv,hs,hli⟩ := hb
  let T : Matrix (Fin d) (Fin d) ℝ := fun i j => v j i
  have hc : LinearIndependent ℝ T.col := hli.map' (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap (by simp)
  have hT := (T.isUnit_iff_isUnit_det.mp (Matrix.linearIndependent_cols_iff_isUnit.mp hc)).ne_zero
  let K := matrixLattice T
  have hK : K = span ℤ (range v) := rfl
  have hKG : K ≤ G := hK ▸ span_le.mpr (range_subset_iff.mpr hv)
  refine ⟨K,hKG,by rw [hK,span_span_of_tower,hs],?_,?_⟩
  · obtain ⟨η,hη,hp⟩ := latticeCoset_uniformlyDiscrete 0 T hT
    exact ⟨η,hη,hp.mono fun x hx => (mem_latticeCoset_iff ..).mpr (by simpa using hx)⟩
  · obtain ⟨U,hU,hr⟩ := matrix_fundamental_region T hT
    obtain ⟨r,_,hb⟩ := hU.subset_closedBall_lt 0 0
    refine ⟨max r 0, le_max_right .., ?_⟩
    rintro q ⟨g,hg,rfl⟩
    obtain ⟨k,hk,hm⟩ := hr g
    exact ⟨g-k,G.sub_mem hg (hKG hk),by rw [map_sub, show K.mkQ k = 0 from (Submodule.Quotient.mk_eq_zero K).mpr hk, sub_zero],
      (show ‖g-k‖ ≤ r by simpa using hb hm).trans (le_max_left ..)⟩

/-- A lattice spanning real space has an element with arbitrarily large
positive value under any nonzero real functional. -/
private theorem exists_large_lattice_value {d : ℕ} {K : Submodule ℤ (Space d)}
    (hK : span ℝ (K : Set (Space d)) = ⊤) (f : Space d →L[ℝ] ℝ) (hf : f ≠ 0) (C : ℝ) :
    ∃ v ∈ K, C < f v := by
  have hex : ∃ w ∈ K, f w ≠ 0 := by
    by_contra! h
    have hz : span ℝ (K : Set (Space d)) ≤ LinearMap.ker f.toLinearMap := span_le.mpr h
    rw [hK,top_le_iff,LinearMap.ker_eq_top] at hz
    exact hf (ContinuousLinearMap.ext fun x => DFunLike.congr_fun hz x)
  obtain ⟨w,hw,hn⟩ := hex
  obtain ⟨v,hv,hpos⟩ : ∃ v ∈ K, 0 < f v := by
    rcases hn.lt_or_gt with h | h
    · exact ⟨-w,K.neg_mem hw,by simpa using h⟩
    · exact ⟨w,hw,h⟩
  obtain ⟨n,hn⟩ := exists_nat_gt (C / f v)
  exact ⟨n • v,K.nsmul_mem hv n,by simpa [nsmul_eq_mul] using (div_lt_iff₀ hpos).mp hn⟩

private theorem translated_residues_injective {d : ℕ} {ι : Type*}
    (H : Submodule ℤ (Space d)) (f : Space d →L[ℝ] ℝ) (hf : ∀ x ∈ H, f x = 0)
    (b : ι → Space d) {r : ℝ} (hb : ∀ i, ‖b i‖ ≤ r)
    (hinj : Function.Injective (fun i => H.mkQ (b i)))
    (v : Space d) (hv : 2 * (‖f‖ * r) < f v) (hr : 0 ≤ r) (m : ℕ) :
    Function.Injective (fun p : Fin m × ι => H.mkQ (b p.2 + p.1.val • v)) := by
  rintro ⟨j,i⟩ ⟨k,l⟩ he
  have h := hf _ ((Submodule.Quotient.eq H).mp he)
  simp only [map_sub,map_add,map_nsmul,nsmul_eq_mul,sub_eq_zero] at h
  have hbound (i) : |f (b i)| ≤ ‖f‖ * r :=
    (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hb i) (norm_nonneg _))
  have hpos : 0 < f v := lt_of_le_of_lt (by positivity) hv
  have hlt (j k : Fin m) (a b : ℝ) (ha : |a| ≤ ‖f‖*r) (hb : |b| ≤ ‖f‖*r) (hjk : j < k) :
      a + (j.val : ℝ)*f v < b + (k.val : ℝ)*f v := by
    have h1 : (j.val : ℝ) + 1 ≤ k.val := by exact_mod_cast (show j.val+1 ≤ k.val from hjk)
    have h2 := mul_le_mul_of_nonneg_right h1 hpos.le
    linarith [(abs_le.mp ha).2,(abs_le.mp hb).1]
  have hejk : j = k := by
    rcases lt_trichotomy j k with h' | h' | h'
    · exact ((hlt j k _ _ (hbound i) (hbound l) h').ne h).elim
    · exact h'
    · exact ((hlt k j _ _ (hbound l) (hbound i) h').ne h.symm).elim
  subst k
  have hiel : i = l := hinj (by simpa [map_add] using he)
  simp [hiel]

/-- A subgroup spanning physical space and satisfying all trigonometric
vanishing relations of the support on one translate lies in a full-rank
lattice. The finite spectral window supplies the upper rank bound. -/
theorem spanning_coset_contained_in_lattice {d : ℕ} {μ : TemperedDistribution (Space d) ℂ}
    {A B : Set (Space d)} {a : A → ℂ} {b : B → ℂ}
    (hμ : HasLocallyAtomicExpansion μ A a) (hA : UniformlyDiscrete A)
    (hν : HasLocallyAtomicExpansion (𝓕 μ) B b) (hB : UniformlyDiscrete B)
    (G : Submodule ℤ (Space d)) (hBG : B ⊆ G) (hG : span ℝ (G : Set (Space d)) = ⊤)
    (t : Space d) (P : Submodule ℤ (Space d)) (hP : span ℝ (P : Set (Space d)) = ⊤)
    (hrel : CosetSatisfiesRelations A G t P) :
    ∃ T : Matrix (Fin d) (Fin d) ℝ, T.det ≠ 0 ∧ P ≤ matrixLattice T := by
  classical
  apply lattice_of_integralDual_span
  let H := integralDual P
  by_contra hn
  obtain ⟨l,hl,hker⟩ := (span ℝ (H : Set (Space d))).exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hn)
  let f := l.toContinuousLinearMap
  have hf (x : Space d) (hx : x ∈ H) : f x = 0 := hker (subset_span hx)
  have hfn : f ≠ 0 := fun he => hl (LinearMap.ext fun x => DFunLike.congr_fun he x)
  obtain ⟨K,hKG,hKspan,hK,r,hr,hrep⟩ := base_lattice G hG
  obtain ⟨M,hM⟩ := character_rank_in_quotient_window hμ hA hν hB K G hK hBG
  obtain ⟨C,hC⟩ := quotient_window_card H (integralDual_uniformlyDiscrete_of_span P hP) r
  obtain ⟨v,hv,hvbig⟩ := exists_large_lattice_value hKspan f hfn (2*(‖f‖*r))
  let m := 2*M*C+1
  obtain ⟨D,hD,hDupper⟩ := hM (r + (m : ℝ) * ‖v‖)
  obtain ⟨F,hF,hFG,hexp⟩ := finite_translations_small_expansion D (G.map K.mkQ).toAddSubgroup hD
  choose w hwG hwq hwr using fun i : F => hrep i.val (hFG i.property)
  let I := Finset.univ.image (fun i : F => H.mkQ (w i))
  have horig (j : I) : ∃ i : F, H.mkQ (w i) = j.val := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp j.property
    exact ⟨i,hi⟩
  choose pick hpick using horig
  let s (j : I) := w (pick j)
  have hs (j : I) : ‖s j‖ ≤ r := hwr _
  have hinj : Function.Injective (fun j : I => H.mkQ (s j)) := fun i j he =>
    Subtype.ext ((hpick i).symm.trans (he.trans (hpick j)))
  have hcount : F.card ≤ C * I.card := by
    obtain ⟨E,hE,hEcard⟩ := hC I
    let index (i : F) : E := ⟨w i,hE _ (hwr i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
    have hi : Function.Injective index := fun i j h => Subtype.ext ((hwq i).symm.trans
      ((congrArg K.mkQ (congrArg Subtype.val h)).trans (hwq j)))
    exact (show F.card ≤ E.card by simpa using Fintype.card_le_of_injective index hi).trans hEcard
  let u (p : Fin m × I) := s p.2 + p.1.val • v
  have huG (p : Fin m × I) : u p ∈ G := G.add_mem (hwG _) (G.nsmul_mem (hKG hv) _)
  have hu (p : Fin m × I) : ‖u p‖ ≤ r + (m : ℝ) * ‖v‖ := by
    apply (norm_add_le ..).trans
    gcongr
    · exact hs _
    · exact (norm_nsmul_le ..).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast p.1.isLt.le) (norm_nonneg v))
  have huF (p : Fin m × I) : K.mkQ (u p) ∈ F := by
    simp only [u,map_add,map_nsmul,show K.mkQ v = 0 from (Submodule.Quotient.mk_eq_zero K).mpr hv,
      nsmul_zero,add_zero,s,hwq]
    exact (pick p.2).property
  have hli := independent_characters_of_coset hrel u huG
    (translated_residues_injective H f hf s hs hinj v hvbig hr m)
  have hupper := (hDupper F u hu huF).trans (Nat.mul_le_mul_left M hexp)
  rw [finrank_span_eq_card hli,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe] at hupper
  have hle : m * I.card ≤ (2*M*C)*I.card := hupper.trans (by
    calc
      _ ≤ M * (2 * (C * I.card)) := by gcongr
      _ = _ := by ring)
  have hI : 0 < I.card := by
    obtain ⟨q,hq⟩ := hF
    exact Finset.card_pos.mpr ⟨_,Finset.mem_image_of_mem _ (Finset.mem_univ (⟨q,hq⟩ : F))⟩
  exact (Nat.le_of_mul_le_mul_right hle hI).not_gt (Nat.lt_succ_self _)

end
end MeyerGeneralProblem.LevOlevskii
