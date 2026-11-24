import UnforcedLeray.Short.PartIIa.Sub.R02_2

/-!
# Part II-a, helpers for `PartII-a:R02/MeanStress/FluctVelSliceBound`

Calculus leaves for the slice bound of the velocity fluctuation (source lines 439-446):

* `fvs_ageDerivIter`: age derivatives of a jointly smooth function are jointly smooth (the proof of
  `AgeDerivSmooth`, restated for a generic normed space `E`).
* `fvs_slice_continuous`, `fvs_hmean_apply`, `fvs_hfluct_apply`: the horizontal mean and the
  fluctuation commute with a coordinate functional of `EuclideanSpace ℝ (Fin 2)`.
* `fvs_iteratedDeriv_clm`: a continuous linear map commutes with the age derivative.
* `fvs_proj_norm`: the coordinate functional has norm at most one.
* `fvs_ageJet_proj_le`: the age-spatial jet of a coordinate of a smooth vector field is bounded by
  the jet of the vector field.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa

open UnforcedLeray.Short.PartI (hmean hfluct ageJet)

/-- Age derivatives of a jointly smooth function are jointly smooth (generic normed space). -/
theorem fvs_ageDerivIter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E → ℝ) (hf : ContDiffOn ℝ ∞ (fun x : ℝ × E => f x.1 x.2) (Ioi 0 ×ˢ univ)) :
    ∀ k : ℕ, ContDiffOn ℝ ∞
      (fun x : ℝ × E => iteratedDeriv k (fun r => f r x.2) x.1) (Ioi 0 ×ˢ univ) := by
  intro k
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set E)) := isOpen_Ioi.prod isOpen_univ
    have hderiv : ∀ x ∈ Ioi (0 : ℝ) ×ˢ (univ : Set E),
        iteratedDeriv (k + 1) (fun r => f r x.2) x.1 =
          fderiv ℝ (fun y : ℝ × E => iteratedDeriv k (fun r => f r y.2) y.1) x (1, 0) := by
      rintro ⟨s, w⟩ hx
      have hs : (0 : ℝ) < s := hx.1
      have hdiff : DifferentiableAt ℝ
          (fun y : ℝ × E => iteratedDeriv k (fun r => f r y.2) y.1) (s, w) :=
        (ih.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
      have hline : HasDerivAt (fun r : ℝ => ((r, w) : ℝ × E)) ((1 : ℝ), (0 : E)) s :=
        (hasDerivAt_id' s).prodMk (hasDerivAt_const s w)
      have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt s hline
      rw [iteratedDeriv_succ]
      exact hcomp.deriv
    have hsm : ContDiffOn ℝ ∞
        (fun y : ℝ × E =>
          fderiv ℝ (fun z : ℝ × E => iteratedDeriv k (fun r => f r z.2) z.1) y (1, 0))
        (Ioi 0 ×ˢ univ) :=
      (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
    exact hsm.congr fun x hx => hderiv x hx

/-- The slice `r ↦ tr.v r` is continuous for `r ≥ 0`. -/
theorem fvs_slice_continuous {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {r : ℝ}
    (hr : 0 ≤ r) : Continuous (fun z : ℝ × ℝ => tr.v r z) := by
  have h : ContinuousOn (fun x : ℝ × (ℝ × ℝ) => tr.v x.1 x.2) (Ici (0 : ℝ) ×ˢ univ) :=
    tr.isTrain.smooth_v.continuousOn
  have hc : Continuous (fun z : ℝ × ℝ => ((r, z) : ℝ × (ℝ × ℝ))) :=
    continuous_const.prodMk continuous_id
  exact h.comp_continuous hc (fun z => mk_mem_prod (mem_Ici.mpr hr) (mem_univ _))

/-- The horizontal mean commutes with a coordinate functional. -/
theorem fvs_hmean_apply (c : ℝ) (a : ℝ × ℝ → EuclideanSpace ℝ (Fin 2))
    (ha : Continuous a) (η : ℝ) (j : Fin 2) :
    (hmean c a η) j = hmean c (fun z => a z j) η := by
  have hint : Integrable (fun q : ℝ => a (q, η)) (volume.restrict (Ioc (-c / 2) (c / 2))) :=
    (ha.comp (continuous_id.prodMk continuous_const)).integrableOn_Ioc
  have h := (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).integral_comp_comm hint
  unfold hmean
  rw [PiLp.smul_apply]
  congr 1
  simpa using h.symm

/-- The fluctuation commutes with a coordinate functional. -/
theorem fvs_hfluct_apply (c : ℝ) (a : ℝ × ℝ → EuclideanSpace ℝ (Fin 2))
    (ha : Continuous a) (j : Fin 2) (z : ℝ × ℝ) :
    hfluct c (fun w => a w j) z = (hfluct c a z) j := by
  unfold hfluct
  rw [PiLp.sub_apply, fvs_hmean_apply c a ha z.2 j]

/-- A continuous linear map commutes with the age derivative of a `C^∞` vector curve. -/
theorem fvs_iteratedDeriv_clm (L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (n : ℕ)
    {g : ℝ → EuclideanSpace ℝ (Fin 2)} {s : ℝ} (hg : ContDiffAt ℝ ∞ g s) :
    iteratedDeriv n (fun r => L (g r)) s = L (iteratedDeriv n g s) := by
  have h := ContinuousLinearMap.iteratedFDeriv_comp_left L hg (i := n) (by exact_mod_cast le_top)
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ n (L ∘ g) s (fun _ => 1) = L (iteratedFDeriv ℝ n g s (fun _ => 1))
  rw [h]
  simp

/-- The coordinate functional has norm at most one. -/
theorem fvs_proj_norm (j : Fin 2) :
    ‖(EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  simpa using PiLp.norm_apply_le x j

/-- **Coordinate of a jet.** For a jointly `C^∞` vector field `G` on `(0,∞) × ℝ²` and a scalar
field `F` whose values are the `j`-th coordinates of `G` for `r > 0`, the age-spatial jet of `F`
is bounded in norm by the age-spatial jet of `G`. -/
theorem fvs_ageJet_proj_le {G : ℝ → ℝ × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hG : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => G x.1 x.2) (Ioi 0 ×ˢ univ))
    (j : Fin 2) (F : ℝ → ℝ × ℝ → ℝ)
    (hFG : ∀ r : ℝ, 0 < r → ∀ z : ℝ × ℝ, F r z = G r z j) (i l : ℕ)
    {s : ℝ} (hs : 0 < s) (z : ℝ × ℝ) :
    ‖ageJet l i F s z‖ ≤ ‖ageJet l i G s z‖ := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  -- the age curve through `z'` is smooth at `s`
  have hGc : ∀ z' : ℝ × ℝ, ContDiffAt ℝ ∞ (fun r => G r z') s := by
    intro z'
    have hm : ContDiffAt ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => G x.1 x.2) (s, z') :=
      hG.contDiffAt (hU.mem_nhds ⟨hs, mem_univ _⟩)
    have hl : ContDiffAt ℝ ∞ (fun r : ℝ => ((r, z') : ℝ × (ℝ × ℝ))) s :=
      contDiffAt_id.prodMk contDiffAt_const
    exact ContDiffAt.comp s hm hl
  -- the age derivative of each coordinate is smooth in the spatial variable
  have hDc : ContDiffAt ℝ ∞ (fun z' => iteratedDeriv l (fun r => G r z') s) z := by
    refine (contDiffAt_piLp 2).2 (fun k => ?_)
    have hck : ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => (G x.1 x.2) k) (Ioi 0 ×ˢ univ) :=
      (contDiffOn_piLp 2).1 hG k
    have hsm := fvs_ageDerivIter (fun r z' => (G r z') k) hck l
    have h2 : ContDiffAt ℝ ∞ (fun z' : ℝ × ℝ => ((s, z') : ℝ × (ℝ × ℝ))) z :=
      contDiffAt_const.prodMk contDiffAt_id
    have hsz : ContDiffAt ℝ ∞
        (fun x : ℝ × (ℝ × ℝ) => iteratedDeriv l (fun r => G r x.2 k) x.1) ((s, z) : ℝ × (ℝ × ℝ)) :=
      hsm.contDiffAt (hU.mem_nhds (show ((s, z) : ℝ × (ℝ × ℝ)) ∈ Ioi (0 : ℝ) ×ˢ univ from
        ⟨hs, mem_univ _⟩))
    have hat : ContDiffAt ℝ ∞ (fun z' => iteratedDeriv l (fun r => G r z' k) s) z :=
      ContDiffAt.comp z hsz h2
    have heq : ∀ z' : ℝ × ℝ,
        (iteratedDeriv l (fun r => G r z') s) k = iteratedDeriv l (fun r => G r z' k) s :=
      fun z' => (fvs_iteratedDeriv_clm (EuclideanSpace.proj k) l (hGc z')).symm
    have hfn : (fun z' : ℝ × ℝ => (iteratedDeriv l (fun r => G r z') s) k) =
        (fun z' => iteratedDeriv l (fun r => G r z' k) s) := funext heq
    rw [hfn]
    exact hat
  -- the scalar profile is the coordinate of the vector profile
  have hfun : (fun z' => iteratedDeriv l (fun r => F r z') s) =
      fun z' => (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
        (iteratedDeriv l (fun r => G r z') s) := by
    funext z'
    have hev : (fun r => F r z') =ᶠ[𝓝 s]
        (fun r => (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) (G r z')) :=
      Filter.eventually_of_mem (Ioi_mem_nhds hs) (fun r hr => by
        dsimp only
        exact hFG r hr z')
    rw [(hev.iteratedDeriv l).eq_of_nhds]
    exact fvs_iteratedDeriv_clm _ l (hGc z')
  -- conclude with the norm of a composition with a coordinate functional
  have hk := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
    (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) hDc
    (show (i : WithTop ℕ∞) ≤ ∞ by exact_mod_cast le_top)
  simp only [UnforcedLeray.Short.PartI.ageJet, UnforcedLeray.Train.jet]
  rw [hfun]
  exact le_trans hk ((mul_le_mul_of_nonneg_right (fvs_proj_norm j) (norm_nonneg _)).trans_eq
    (one_mul _))

end UnforcedLeray.Short.PartIIa
