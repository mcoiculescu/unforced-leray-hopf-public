import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.PtOrg

/-!
# `PartIII-b:C/rep/8/2/3/2/3`: the age jets from the joint derivative `ageJetLeJoint`

Source of record: `the November 2 reference manuscript` 5464-5465 (generic calculus).
The age derivative `∂_s` is the first-coordinate derivative `fderiv G x (1,0)`, so induction on the
age order `ℓ` moves one derivative from the age jet to the joint derivative, while the spatial
slice at a fixed age is the joint derivative restricted along the isometric embedding
`z ↦ (s,z)` (a composition with a shift and the right inclusion `inr`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Cyl (Plane)

/-- The spatial jet at fixed age is bounded by the joint jet at the same point. -/
theorem alj_slice_le {G : ℝ × Plane → ℝ}
    (hG : ContDiffOn ℝ ∞ G (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)))
    (m : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane) :
    ‖iteratedFDeriv ℝ m (fun z' : Plane => G (s, z')) z‖ ≤ ‖iteratedFDeriv ℝ m G (s, z)‖ := by
  set a : ℝ × Plane := (s, (0, 0)) with ha
  set V : Set (ℝ × Plane) := (fun y : ℝ × Plane => y + a) ⁻¹' (Ioi (0 : ℝ) ×ˢ (univ : Set Plane))
    with hV
  set f2 : ℝ × Plane → ℝ := fun y => G (y + a) with hf2
  have hVo : IsOpen V :=
    IsOpen.preimage (continuous_id.add continuous_const) (isOpen_Ioi.prod isOpen_univ)
  have hf2C : ContDiffOn ℝ ∞ f2 V :=
    hG.comp (contDiff_id.add contDiff_const).contDiffOn (fun y hy => hy)
  set g : Plane →L[ℝ] (ℝ × Plane) := ContinuousLinearMap.inr ℝ ℝ Plane with hg
  have hmem : ∀ z' : Plane, g z' ∈ V := fun z' => by
    refine ⟨?_, mem_univ _⟩
    show (0 : ℝ) < 0 + s
    rw [zero_add]
    exact hs
  have hcomp : (fun z' : Plane => G (s, z')) = f2 ∘ g := by
    funext z'
    show G (s, z') = G (((0 : ℝ), z') + a)
    congr 1
    rw [ha]
    exact Prod.ext (zero_add s).symm (add_zero z').symm
  have hgV : g ⁻¹' V = univ := Set.eq_univ_of_forall hmem
  have hz : g z ∈ V := hmem z
  have key := ContinuousLinearMap.iteratedFDerivWithin_comp_right g hf2C hVo.uniqueDiffOn
    (by rw [hgV]; exact uniqueDiffOn_univ) hz (i := m) (by exact_mod_cast le_top)
  rw [hgV, iteratedFDerivWithin_univ,
    iteratedFDerivWithin_of_isOpen m hVo hz] at key
  have hg1 : ‖g‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one ℝ ℝ Plane
  have hpt : g z + a = (s, z) := by
    show ((0 : ℝ), z) + a = (s, z)
    rw [ha]
    exact Prod.ext (zero_add s) (add_zero z)
  have hshift : iteratedFDeriv ℝ m f2 (g z) = iteratedFDeriv ℝ m G (s, z) := by
    rw [hf2, iteratedFDeriv_comp_add_right, hpt]
  rw [hcomp, key, ← hshift]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin m, ‖g‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hg1)
  calc ‖iteratedFDeriv ℝ m f2 (g z)‖ * ∏ _i : Fin m, ‖g‖
      ≤ ‖iteratedFDeriv ℝ m f2 (g z)‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ m f2 (g z)‖ := mul_one _

/-- The age derivative of `G` is the first-coordinate Fréchet derivative. -/
theorem alj_deriv_eq {G : ℝ × Plane → ℝ}
    (hG : ContDiffOn ℝ ∞ G (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)))
    {x : ℝ × Plane} (hx : 0 < x.1) :
    deriv (fun r : ℝ => G (r, x.2)) x.1 = fderiv ℝ G x ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hxU : x ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := ⟨hx, mem_univ _⟩
  have hd : DifferentiableAt ℝ G x :=
    (hG.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
  have hl : HasDerivAt (fun r : ℝ => (r, x.2)) ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) x.1 :=
    (hasDerivAt_id' x.1).prodMk (hasDerivAt_const x.1 x.2)
  exact (hd.hasFDerivAt.comp_hasDerivAt x.1 hl).deriv

/-- One derivative from the joint `fderiv` costs one order of the joint derivative. -/
theorem alj_fderiv_le {G : ℝ × Plane → ℝ}
    (hG : ContDiffOn ℝ ∞ G (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)))
    (n : ℕ) {y : ℝ × Plane} (hy : 0 < y.1) :
    ‖iteratedFDeriv ℝ n (fun x : ℝ × Plane => fderiv ℝ G x ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) y‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) G y‖ := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hyU : y ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := ⟨hy, mem_univ _⟩
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ G) y :=
    ((hG.fderiv_of_isOpen hU (by simp)).contDiffAt (hU.mem_nhds hyU))
  have h1 := norm_iteratedFDeriv_clm_apply_const (c := ((1 : ℝ), ((0 : ℝ), (0 : ℝ))))
    (n := n) hfd (by exact_mod_cast le_top)
  have h2 : ‖iteratedFDeriv ℝ n (fderiv ℝ G) y‖ = ‖iteratedFDeriv ℝ (n + 1) G y‖ :=
    norm_iteratedFDeriv_fderiv
  have hc : ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ ≤ 1 := by
    simp [Prod.norm_def]
  calc ‖iteratedFDeriv ℝ n (fun x : ℝ × Plane => fderiv ℝ G x ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) y‖
      ≤ ‖((1 : ℝ), ((0 : ℝ), (0 : ℝ)))‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ G) y‖ := h1
    _ ≤ 1 * ‖iteratedFDeriv ℝ n (fderiv ℝ G) y‖ :=
        mul_le_mul_of_nonneg_right hc (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (n + 1) G y‖ := by rw [one_mul, h2]

/-- The age jets of a jointly smooth field are bounded by the joint jet (induction on `ℓ`). -/
theorem alj_main : ∀ (ℓ : ℕ) (F : ℝ → Plane → ℝ),
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => F x.1 x.2) (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) →
    ∀ (m : ℕ) {s : ℝ} (hs : 0 < s) (z : Plane),
      ‖UnforcedLeray.Short.PartI.ageJet ℓ m F s z‖ ≤
        ‖iteratedFDeriv ℝ (ℓ + m) (fun x : ℝ × Plane => F x.1 x.2) (s, z)‖ := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro F hF m s hs z
    rw [zero_add]
    have h0 : (fun z' : Plane => iteratedDeriv 0 (fun r => F r z') s) = fun z' => F s z' := by
      funext z'
      rw [iteratedDeriv_zero]
    show ‖iteratedFDeriv ℝ m (fun z' : Plane => iteratedDeriv 0 (fun r => F r z') s) z‖ ≤ _
    rw [h0]
    exact alj_slice_le (G := fun x : ℝ × Plane => F x.1 x.2) hF m hs z
  | succ ℓ ih =>
    intro F hF m s hs z
    have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
    have hyU : (s, z) ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := ⟨hs, mem_univ _⟩
    have hKC : ContDiffOn ℝ ∞
        (fun x : ℝ × Plane => fderiv ℝ (fun x : ℝ × Plane => F x.1 x.2) x
          ((1 : ℝ), ((0 : ℝ), (0 : ℝ))))
        (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :=
      (hF.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
    have hF'C : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => (fun r z' => deriv (fun r' => F r' z') r) x.1 x.2)
        (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :=
      hKC.congr (fun x hx => alj_deriv_eq hF hx.1)
    have ihF := ih (fun r z' => deriv (fun r' => F r' z') r) hF'C m hs z
    have hAJ : UnforcedLeray.Short.PartI.ageJet (ℓ + 1) m F s z =
        UnforcedLeray.Short.PartI.ageJet ℓ m (fun r z' => deriv (fun r' => F r' z') r) s z := by
      have hfun : (fun z' : Plane => iteratedDeriv (ℓ + 1) (fun r => F r z') s) =
          (fun z' : Plane => iteratedDeriv ℓ (fun r => deriv (fun r' => F r' z') r) s) := by
        funext z'
        rw [iteratedDeriv_succ']
      show iteratedFDeriv ℝ m (fun z' : Plane => iteratedDeriv (ℓ + 1) (fun r => F r z') s) z =
        iteratedFDeriv ℝ m (fun z' : Plane => iteratedDeriv ℓ (fun r => deriv (fun r' => F r' z') r) s) z
      rw [hfun]
    rw [hAJ]
    refine ihF.trans ?_
    have heq : (fun x : ℝ × Plane => (fun r z' => deriv (fun r' => F r' z') r) x.1 x.2) =ᶠ[𝓝 (s, z)]
        (fun x : ℝ × Plane => fderiv ℝ (fun x : ℝ × Plane => F x.1 x.2) x
          ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hyU) (fun x hx => alj_deriv_eq hF hx.1)
    rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) heq (ℓ + m)).self_of_nhds]
    have hstep := alj_fderiv_le (G := fun x : ℝ × Plane => F x.1 x.2) hF (ℓ + m) (y := (s, z)) hs
    rw [show ℓ + 1 + m = ℓ + m + 1 by omega]
    exact hstep

/-- **Target** `ageJetLeJoint`: the age jets are bounded by the joint derivative (`AgeJetLeJoint`). -/
theorem ageJetLeJoint : AgeJetLeJoint := by
  intro F hF ℓ m s hs z
  exact alj_main ℓ F hF m hs z

end UnforcedLeray.Short.PartIIIb.Concrete
