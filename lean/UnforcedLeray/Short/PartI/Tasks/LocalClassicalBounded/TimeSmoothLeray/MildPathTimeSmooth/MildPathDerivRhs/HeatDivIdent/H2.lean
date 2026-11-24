import UnforcedLeray.Short.PartI.Sub.PartI_T02_1_4_4_1_5
import UnforcedLeray.Lib.TrainB.P0H3Range
import UnforcedLeray.Lib.CylinderB.ModePairing

/-!
# `WeakDivZeroH5`: a `P₀`-fixed `H^5` field is weakly divergence free

Source: the weak-derivative calculus of the periodic cylinder scale used in
`the November 2 reference manuscript`, lines 261-288 (mild solution lives in every
`H^k`, solenoidal).  The route: value of `P₀ w₃` lies in `Cyl.divFree`; the weak derivative
identity of `w ∈ H^5` against periodic tests converts the `gradL`-pairings into
`∫ φ · div w`; the fundamental lemma (`HasWeakDeriv.ae_unique` for the empty word) finishes.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

theorem weightedToCell_coeFn (c : ℝ)
    (f : MeasureTheory.Lp Cyl.Vec2 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)))) :
    ((weightedToCellL2Isometry c f : Cyl.L2v c) : Plane → Cyl.Vec2) =ᵐ[Cyl.cellμ c]
      (f : Plane → Cyl.Vec2) := by
  unfold weightedToCellL2Isometry
  exact Lp.coeFn_compMeasurePreserving f _


/-- Weak derivative of the `i`-th component: the `i`-th partial of `w ∈ H^5` is the weak
`∂_i`-derivative of its value. -/
theorem hw_deriv (c : ℝ) (w : Cyl.H ℝ Cyl.Vec2 c 0 5) (i : Fin 2) (j : Fin 2) :
    Sob.HasWeakDeriv (Sob.cylinder c) [Sob.cylDir i]
      (fun z => hVal (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) z j)
      (fun z => hVal (Sob.W.partialDeriv (k := 4) i w) z j) := by
  have h := Sob.W.hasWeakDeriv w (Sob.Idx.cons i (Sob.Idx.zero : Sob.Idx 2 4))
  have hword : (Sob.cylinder c).word (Sob.Idx.cons i (Sob.Idx.zero : Sob.Idx 2 4)) =
      [Sob.cylDir i] := by
    simp [Sob.TestDomain.word_cons, Sob.TestDomain.word_zero]
  rw [hword] at h
  exact h.map_clm (EuclideanSpace.proj j : Cyl.Vec2 →L[ℝ] ℝ)

theorem wμ0_eq (c : ℝ) :
    Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) = Cyl.cellμ c := by
  rw [Cyl.wμ_ρwW, Cyl.wμ]
  have h1 : (fun z => ENNReal.ofReal (Cyl.ρw c z ^ (0 : ℝ))) = 1 := by
    funext z; simp
  rw [h1, MeasureTheory.withDensity_one]

theorem memLp_hVal_comp {c : ℝ} {m : ℕ} (x : Cyl.H ℝ Cyl.Vec2 c 0 m) (j : Fin 2) :
    MemLp (fun z => hVal x z j) 2 (Cyl.cellμ c) := by
  have h := (EuclideanSpace.proj j : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp'
    (MeasureTheory.Lp.memLp
      (Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 x))
  exact h.mono_measure (wμ0_eq c).ge


theorem integrable_test_mul_cell {c : ℝ} {φ g : Plane → ℝ} (hφ : Sob.IsCylTest c φ)
    (hg : MemLp g 2 (Cyl.cellμ c)) : Integrable (fun z => φ z * g z) (Cyl.cellμ c) :=
  Cyl.integrableOn_test_mul hφ hg

/-- Integration by parts for the `i`-th component against a periodic test. -/
theorem ibp_comp (c : ℝ) (w : Cyl.H ℝ Cyl.Vec2 c 0 5) (i : Fin 2) {φ : Plane → ℝ}
    (hφ : Sob.IsCylTest c φ) :
    ∫ z, fderiv ℝ φ z (Sob.cylDir i) *
        hVal (Sob.W.restrict (by norm_num : 3 ≤ 5) w : Cyl.H ℝ Cyl.Vec2 c 0 3) z i ∂(Cyl.cellμ c) =
      -∫ z, φ z * hVal (Sob.W.partialDeriv (k := 4) i w) z i ∂(Cyl.cellμ c) := by
  have h := (hw_deriv c w i i).identity φ hφ
  simp only [Sob.iterDirDeriv_singleton, smul_eq_mul, List.length_singleton, pow_one,
    neg_one_mul, Cyl.cylinder_μ_eq] at h
  exact h

theorem weakDivZeroH5 : WeakDivZeroH5 := by
  intro c hc w hP
  set w3 : Cyl.H ℝ Cyl.Vec2 c 0 3 := Sob.W.restrict (by norm_num : 3 ≤ 5) w with hw3
  set g : Plane → ℝ := fun z => ∑ i : Fin 2, hVal (Sob.W.partialDeriv (k := 4) i w) z i with hg
  have hgmem : MemLp g 2 (Cyl.cellμ c) := by
    have : g = fun z => ∑ i ∈ Finset.univ, hVal (Sob.W.partialDeriv (k := 4) i w) z i := rfl
    rw [this]
    exact memLp_finsetSum Finset.univ fun i _ => memLp_hVal_comp _ i
  have hmem := P0H3CLM_value_mem_divFree hc w3
  rw [hP, Cyl.mem_divFree] at hmem
  have hv : ((vecH3CellDerivCLM (c := c) Sob.Idx.zero w3 : Cyl.L2v c) : Plane → Cyl.Vec2)
      =ᵐ[Cyl.cellμ c] hVal w3 :=
    weightedToCell_coeFn c _
  have key : ∀ φ : Plane → ℝ, Sob.IsCylTest c φ → ∫ z, φ z * g z ∂(Cyl.cellμ c) = 0 := by
    intro φ hφ
    have h0 := hmem φ hφ
    rw [Cyl.gradL, L2.inner_def] at h0
    have e1 : ∫ z, inner ℝ (((Cyl.memLp_gradT hφ).toLp (Cyl.gradT φ) : Plane → Cyl.Vec2) z)
          ((vecH3CellDerivCLM (c := c) Sob.Idx.zero w3 : Cyl.L2v c) z) ∂(Cyl.cellμ c) =
        ∫ z, ∑ i : Fin 2, fderiv ℝ φ z (Sob.cylDir i) * hVal w3 z i ∂(Cyl.cellμ c) := by
      refine integral_congr_ae ?_
      filter_upwards [(Cyl.memLp_gradT hφ).coeFn_toLp, hv] with z h1 h2
      rw [h1, h2, real_inner_comm, Cyl.gradT, Cyl.inner_vec, Fin.sum_univ_two,
        Cyl.partialQ_eq_fderiv (hφ.differentiable), Cyl.partialEta_eq_fderiv (hφ.differentiable)]
      simp [Sob.cylDir, mul_comm]
    rw [e1] at h0
    have hint : ∀ i : Fin 2, Integrable (fun z => fderiv ℝ φ z (Sob.cylDir i) * hVal w3 z i)
        (Cyl.cellμ c) := by
      intro i
      have hd : Sob.IsCylTest c (fun z => fderiv ℝ φ z (Sob.cylDir i)) := hφ.dirDeriv _
      exact integrable_test_mul_cell hd (memLp_hVal_comp w3 i)
    have hint2 : ∀ i : Fin 2, Integrable (fun z => φ z * hVal (Sob.W.partialDeriv (k := 4) i w) z i)
        (Cyl.cellμ c) := fun i => integrable_test_mul_cell hφ (memLp_hVal_comp _ i)
    rw [integral_finset_sum _ (fun i _ => hint i)] at h0
    have : ∫ z, φ z * g z ∂(Cyl.cellμ c) =
        ∑ i : Fin 2, ∫ z, φ z * hVal (Sob.W.partialDeriv (k := 4) i w) z i ∂(Cyl.cellμ c) := by
      rw [← integral_finset_sum _ (fun i _ => hint2 i)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp [hg, mul_add]
    rw [this]
    have h3 : ∀ i : Fin 2, ∫ z, φ z * hVal (Sob.W.partialDeriv (k := 4) i w) z i ∂(Cyl.cellμ c) =
        -∫ z, fderiv ℝ φ z (Sob.cylDir i) * hVal w3 z i ∂(Cyl.cellμ c) := fun i => by
      rw [ibp_comp c w i hφ, neg_neg]
    simp only [h3, Finset.sum_neg_distrib, h0, neg_zero]
  -- fundamental lemma
  have h1 : Sob.HasWeakDeriv (Sob.cylinder c) [] (0 : Plane → ℝ) g := by
    refine ⟨fun φ _ => by simpa using (integrable_zero Plane ℝ (Sob.cylinder c).μ),
      fun φ hφ => ?_, fun φ hφ => ?_⟩
    · have := integrable_test_mul_cell hφ hgmem
      simp only [smul_eq_mul]
      rw [Cyl.cylinder_μ_eq]
      exact this
    · have := key φ hφ
      simp only [Sob.iterDirDeriv_nil, Pi.zero_apply, smul_zero, integral_zero, List.length_nil,
        pow_zero, one_smul, smul_eq_mul]
      rw [Cyl.cylinder_μ_eq, one_mul, this]
      exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => by simp)
  have hloc : LocallyIntegrable g (Sob.cylinder c).μ := by
    exact Sob.locallyIntegrable_of_memLp (ρ := (1 : Sob.Weight Plane)) (p := 2)
      (Cyl.memLp_cell_of_wμ_one hgmem)
  have := h1.ae_unique (Sob.HasWeakDeriv.zero) hloc (locallyIntegrable_zero)
  rw [Cyl.cylinder_μ_eq] at this
  filter_upwards [this] with z hz
  simpa [hg] using hz

end UnforcedLeray.Short.PartI
