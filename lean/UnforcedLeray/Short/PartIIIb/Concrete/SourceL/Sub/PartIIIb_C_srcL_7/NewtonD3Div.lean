import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Sub.PartIIIb_C_srcL_7.NewtonLap
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.NewtonD3

/-!
# `NewtonD3Div`: the divergence of the third Newton derivative vanishes (task `PartIII-b:C/srcL/7/8`)

Source of record: `the November 2 reference manuscript`, lines 4797-4800.
Route: `D_a G := fun x => fderiv G x e_a`; `newtonD3 x i j k = D_i D_j D_k N x`.  Off `0` all
iterates are smooth, the Schwarz symmetry `D_a D_b G = D_b D_a G` holds pointwise, and
`Σ_i D_i D_i N = 0` (`newtonLap`) on the open set `{x ≠ 0}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- The coordinate derivative `D_a G = ∂_a G`. -/
def DaxD (a : Fin 3) (G : Vec3 → ℝ) : Vec3 → ℝ := fun x => fderiv ℝ G x (Pi.single a 1)

theorem diffAt_of_smoothD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Vec3 → E}
    (hF : ContDiffOn ℝ NewtonD3.ii F NewtonD3.punct) {x : Vec3} (hx : x ≠ 0) :
    DifferentiableAt ℝ F x :=
  (hF.contDiffAt (NewtonD3.isOpen_punct.mem_nhds hx)).differentiableAt (by simp [NewtonD3.ii])

theorem DaxD_smooth {G : Vec3 → ℝ} (hG : ContDiffOn ℝ NewtonD3.ii G NewtonD3.punct) (a : Fin 3) :
    ContDiffOn ℝ NewtonD3.ii (DaxD a G) NewtonD3.punct :=
  (hG.fderiv_of_isOpen NewtonD3.isOpen_punct (by simp [NewtonD3.ii])).clm_apply contDiffOn_const

/-- Schwarz symmetry of the coordinate derivatives off `0`. -/
theorem swap_ptD {G : Vec3 → ℝ} (hG : ContDiffOn ℝ NewtonD3.ii G NewtonD3.punct) {x : Vec3}
    (hx : x ≠ 0) (a b : Fin 3) : DaxD a (DaxD b G) x = DaxD b (DaxD a G) x := by
  have hc : ContDiffAt ℝ NewtonD3.ii G x := hG.contDiffAt (NewtonD3.isOpen_punct.mem_nhds hx)
  have hsym : IsSymmSndFDerivAt ℝ G x :=
    hc.isSymmSndFDerivAt (by simp [NewtonD3.ii])
  have hF : ContDiffOn ℝ NewtonD3.ii (fderiv ℝ G) NewtonD3.punct :=
    hG.fderiv_of_isOpen NewtonD3.isOpen_punct (by simp [NewtonD3.ii])
  have hdF : DifferentiableAt ℝ (fderiv ℝ G) x := diffAt_of_smoothD hF hx
  show fderiv ℝ (fun y => fderiv ℝ G y (Pi.single b 1)) x (Pi.single a 1) =
    fderiv ℝ (fun y => fderiv ℝ G y (Pi.single a 1)) x (Pi.single b 1)
  rw [fderiv_clm_apply hdF (differentiableAt_const _), fderiv_clm_apply hdF (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.zero_apply, zero_add, add_zero, ContinuousLinearMap.flip_apply]
  exact hsym _ _

/-- Equality off `0` gives equality of directional derivatives off `0`. -/
theorem congrFD {f g : Vec3 → ℝ} (h : ∀ y : Vec3, y ≠ 0 → f y = g y) {x : Vec3} (hx : x ≠ 0)
    (v : Vec3) : fderiv ℝ f x v = fderiv ℝ g x v := by
  have : f =ᶠ[𝓝 x] g := by
    have hs : Set.EqOn f g NewtonD3.punct := by
      intro y hy
      exact h y hy
    exact hs.eventuallyEq_of_mem (NewtonD3.isOpen_punct.mem_nhds hx)
  rw [this.fderiv_eq]

theorem fderiv_eq_zero_of {f : Vec3 → ℝ} (h : ∀ y : Vec3, y ≠ 0 → f y = 0) {x : Vec3}
    (hx : x ≠ 0) (v : Vec3) : fderiv ℝ f x v = 0 := by
  have := congrFD (g := fun _ => (0 : ℝ)) h hx v
  rw [this]
  simp

theorem chainC {G : Vec3 → ℝ} (hG : ContDiffOn ℝ NewtonD3.ii G NewtonD3.punct) {w : Vec3}
    (hw : w ≠ 0) (i j : Fin 3) :
    DaxD i (DaxD i (DaxD j G)) w = DaxD j (DaxD i (DaxD i G)) w := by
  have hH : ContDiffOn ℝ NewtonD3.ii (DaxD i G) NewtonD3.punct := DaxD_smooth hG i
  calc DaxD i (DaxD i (DaxD j G)) w = fderiv ℝ (DaxD i (DaxD j G)) w (Pi.single i 1) := rfl
    _ = fderiv ℝ (DaxD j (DaxD i G)) w (Pi.single i 1) :=
        congrFD (f := DaxD i (DaxD j G)) (g := DaxD j (DaxD i G))
          (fun y hy => swap_ptD hG hy i j) hw _
    _ = DaxD i (DaxD j (DaxD i G)) w := rfl
    _ = DaxD j (DaxD i (DaxD i G)) w := swap_ptD hH hw i j

theorem chainD {x : Vec3} (hx : x ≠ 0) (i k : Fin 3) :
    DaxD i (DaxD i (DaxD k newtonN)) x = DaxD k (DaxD i (DaxD i newtonN)) x := by
  have hN : ContDiffOn ℝ NewtonD3.ii newtonN NewtonD3.punct := NewtonD3.newtonN_contDiffOn
  have hHi : ContDiffOn ℝ NewtonD3.ii (DaxD i newtonN) NewtonD3.punct := DaxD_smooth hN i
  calc DaxD i (DaxD i (DaxD k newtonN)) x = fderiv ℝ (DaxD i (DaxD k newtonN)) x (Pi.single i 1) := rfl
    _ = fderiv ℝ (DaxD k (DaxD i newtonN)) x (Pi.single i 1) :=
        congrFD (f := DaxD i (DaxD k newtonN)) (g := DaxD k (DaxD i newtonN))
          (fun y hy => swap_ptD hN hy i k) hx _
    _ = DaxD i (DaxD k (DaxD i newtonN)) x := rfl
    _ = DaxD k (DaxD i (DaxD i newtonN)) x := swap_ptD hHi hx i k

theorem newtonD3Div : NewtonD3Div := by
  intro w hw j k
  have hN : ContDiffOn ℝ NewtonD3.ii newtonN NewtonD3.punct := NewtonD3.newtonN_contDiffOn
  have hG : ContDiffOn ℝ NewtonD3.ii (DaxD k newtonN) NewtonD3.punct := DaxD_smooth hN k
  have hQ : ∀ i : Fin 3, ContDiffOn ℝ NewtonD3.ii (DaxD i (DaxD i newtonN)) NewtonD3.punct :=
    fun i => DaxD_smooth (DaxD_smooth hN i) i
  have hterm : ∀ i : Fin 3, fderiv ℝ (fun x => newtonD3 x i j k) w (Pi.single i 1) =
      DaxD j (DaxD k (DaxD i (DaxD i newtonN))) w := by
    intro i
    have e : (fun x => newtonD3 x i j k) = DaxD i (DaxD j (DaxD k newtonN)) := rfl
    rw [e]
    show DaxD i (DaxD i (DaxD j (DaxD k newtonN))) w = _
    rw [chainC hG hw i j]
    exact congrFD (f := DaxD i (DaxD i (DaxD k newtonN)))
      (g := DaxD k (DaxD i (DaxD i newtonN))) (fun y hy => chainD hy i k) hw (Pi.single j 1)
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  have hdiffQ : ∀ i : Fin 3, DifferentiableAt ℝ (DaxD k (DaxD i (DaxD i newtonN))) w :=
    fun i => diffAt_of_smoothD (DaxD_smooth (hQ i) k) hw
  have hS : ∀ y : Vec3, y ≠ 0 → ∑ i, DaxD i (DaxD i newtonN) y = 0 :=
    fun y hy => newtonLap y hy
  have hRy : ∀ y : Vec3, y ≠ 0 → ∑ i, DaxD k (DaxD i (DaxD i newtonN)) y = 0 := by
    intro y hy
    have hd : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        DifferentiableAt ℝ (fun z => DaxD i (DaxD i newtonN) z) y :=
      fun i _ => diffAt_of_smoothD (hQ i) hy
    have h1 : fderiv ℝ (fun z => ∑ i, DaxD i (DaxD i newtonN) z) y (Pi.single k 1) = 0 :=
      fderiv_eq_zero_of (fun z hz => hS z hz) hy _
    rw [fderiv_fun_sum hd] at h1
    simp only [sum_apply] at h1
    exact h1
  have hfin : ∑ i, DaxD j (DaxD k (DaxD i (DaxD i newtonN))) w =
      fderiv ℝ (fun y => ∑ i, DaxD k (DaxD i (DaxD i newtonN)) y) w (Pi.single j 1) := by
    rw [fderiv_fun_sum (fun i _ => hdiffQ i)]
    simp only [sum_apply]
    rfl
  rw [hfin]
  exact fderiv_eq_zero_of hRy hw _

end UnforcedLeray.Short.PartIIIb.Concrete
