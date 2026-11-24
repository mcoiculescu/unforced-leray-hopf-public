import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Train.Defs
import UnforcedLeray.Units.B0238

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The `ρ`-derivative word `[0]` at an interior point is the age derivative of the slice. -/
theorem tjW_zero_apply_int {G : ℝ × (ℝ × ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G tjU) {ρ : ℝ}
    (hρ : 0 < ρ) (x : ℝ × ℝ) : tjW [0] G (ρ, x) = deriv (fun t : ℝ => G (t, x)) ρ := by
  have hp : ((ρ, x) : ℝ × (ℝ × ℝ)) ∈ tjU := ⟨mem_Ici.2 hρ.le, mem_univ x⟩
  have hnhds : tjU ∈ 𝓝 ((ρ, x) : ℝ × (ℝ × ℝ)) := by
    apply Filter.mem_of_superset ((isOpen_Ioi.prod isOpen_univ).mem_nhds
      (⟨hρ, mem_univ x⟩ : ((ρ, x) : ℝ × (ℝ × ℝ)) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    intro q hq
    exact ⟨mem_Ici.2 (le_of_lt hq.1), mem_univ _⟩
  have hd : HasFDerivWithinAt G (fderivWithin ℝ G tjU (ρ, x)) tjU (ρ, x) :=
    (hG.differentiableOn (by simp) _ hp).hasFDerivWithinAt
  have hF : HasFDerivAt G (fderivWithin ℝ G tjU (ρ, x)) (ρ, x) := hd.hasFDerivAt hnhds
  have hγ : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × (ℝ × ℝ))) ((1, (0, 0)) : ℝ × (ℝ × ℝ)) ρ :=
    (hasDerivAt_id ρ).prodMk (hasDerivAt_const ρ x)
  have e : deriv (fun t : ℝ => G (t, x)) ρ =
      fderivWithin ℝ G tjU (ρ, x) ((1, (0, 0)) : ℝ × (ℝ × ℝ)) :=
    (hF.comp_hasDerivAt ρ hγ).deriv
  rw [e]
  rfl

/-- The word `[1, 1]` is the second `q`-slice derivative. -/
theorem tjW_one_one {G : ℝ × (ℝ × ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G tjU) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (x : ℝ × ℝ) :
    tjW [1, 1] G (ρ, x) = UnforcedLeray.Cyl.partialQ
      (UnforcedLeray.Cyl.partialQ (fun z : ℝ × ℝ => G (ρ, z))) x := by
  have hG' : ContDiffOn ℝ ∞ (tjW [1] G) tjU := tjW_contDiffOn hG [1]
  have hfun : (fun t : ℝ => tjW [1] G (ρ, (t, x.2))) =
      (fun t : ℝ => UnforcedLeray.Cyl.partialQ (fun z : ℝ × ℝ => G (ρ, z)) (t, x.2)) :=
    funext fun t => tjW_one_apply hG hρ (t, x.2)
  have h1 : tjW [1, 1] G (ρ, x) = tjW [1] (tjW [1] G) (ρ, x) := rfl
  rw [h1, tjW_one_apply hG' hρ x, hfun]
  rfl

/-- The word `[2, 2]` is the second `η`-slice derivative. -/
theorem tjW_two_two {G : ℝ × (ℝ × ℝ) → ℝ} (hG : ContDiffOn ℝ ∞ G tjU) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (x : ℝ × ℝ) :
    tjW [2, 2] G (ρ, x) = UnforcedLeray.Cyl.partialEta
      (UnforcedLeray.Cyl.partialEta (fun z : ℝ × ℝ => G (ρ, z))) x := by
  have hG' : ContDiffOn ℝ ∞ (tjW [2] G) tjU := tjW_contDiffOn hG [2]
  have hfun : (fun t : ℝ => tjW [2] G (ρ, (x.1, t))) =
      (fun t : ℝ => UnforcedLeray.Cyl.partialEta (fun z : ℝ × ℝ => G (ρ, z)) (x.1, t)) :=
    funext fun t => tjW_two_apply hG hρ (x.1, t)
  have h1 : tjW [2, 2] G (ρ, x) = tjW [2] (tjW [2] G) (ρ, x) := rfl
  rw [h1, tjW_two_apply hG' hρ x, hfun]
  rfl

/-- **The train vorticity equation as a word identity** (SP 270-288, 2081-2084): `E = curl v` is
`C^∞` on `tjU`, its `q`, `η` slice words are the curl of `v`, and the age derivative is the
vorticity equation. -/
theorem tjTrainVort : TjTrainVort := by
  intro ν c tr
  have hV1 : ContDiffOn ℝ ∞ (tjV tr 1) tjU :=
    ((EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff).comp_contDiffOn
      tr.isTrain.smooth_v
  have hV0 : ContDiffOn ℝ ∞ (tjV tr 0) tjU :=
    ((EuclideanSpace.proj (0 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff).comp_contDiffOn
      tr.isTrain.smooth_v
  have hcl2 : ∀ p ∈ tjU, tjE tr p = tjW [1] (tjV tr 1) p - tjW [2] (tjV tr 0) p := by
    rintro ⟨ρ, x⟩ hp
    have hρ : 0 ≤ ρ := hp.1
    rw [tjW_one_apply hV1 hρ x, tjW_two_apply hV0 hρ x]
    rfl
  have hE1 : ContDiffOn ℝ ∞ (tjE tr) tjU :=
    ((tjW_contDiffOn hV1 [1]).sub (tjW_contDiffOn hV0 [2])).congr
      (fun p hp => hcl2 p hp)
  have hpos : ∀ p ∈ (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))),
      tjW [0] (tjE tr) p = ν * (tjW [1, 1] (tjE tr) p + tjW [2, 2] (tjE tr) p) -
        (tjV tr 0 p * tjW [1] (tjE tr) p + tjV tr 1 p * tjW [2] (tjE tr) p) := by
    rintro ⟨ρ, x⟩ ⟨hρ, -⟩
    have hρ' : (0 : ℝ) < ρ := hρ
    have h0 : tjW [0] (tjE tr) (ρ, x) =
        deriv (fun t : ℝ => UnforcedLeray.B0238.Ec tr t x) ρ :=
      tjW_zero_apply_int hE1 hρ' x
    have h1 : tjW [1] (tjE tr) (ρ, x) =
        UnforcedLeray.Cyl.partialQ (UnforcedLeray.B0238.Ec tr ρ) x :=
      tjW_one_apply hE1 hρ'.le x
    have h2 : tjW [2] (tjE tr) (ρ, x) =
        UnforcedLeray.Cyl.partialEta (UnforcedLeray.B0238.Ec tr ρ) x :=
      tjW_two_apply hE1 hρ'.le x
    have h11 : tjW [1, 1] (tjE tr) (ρ, x) =
        UnforcedLeray.Cyl.partialQ (UnforcedLeray.Cyl.partialQ (UnforcedLeray.B0238.Ec tr ρ)) x :=
      tjW_one_one hE1 hρ'.le x
    have h22 : tjW [2, 2] (tjE tr) (ρ, x) =
        UnforcedLeray.Cyl.partialEta (UnforcedLeray.Cyl.partialEta
          (UnforcedLeray.B0238.Ec tr ρ)) x :=
      tjW_two_two hE1 hρ'.le x
    have hEc := UnforcedLeray.B0238.Ec_vorticity_equation tr hρ' x
    unfold UnforcedLeray.Train.lapS at hEc
    rw [h0, h1, h2, h11, h22]
    show deriv (fun t : ℝ => UnforcedLeray.B0238.Ec tr t x) ρ =
      ν * (UnforcedLeray.Cyl.partialQ (UnforcedLeray.Cyl.partialQ (UnforcedLeray.B0238.Ec tr ρ)) x +
        UnforcedLeray.Cyl.partialEta (UnforcedLeray.Cyl.partialEta
          (UnforcedLeray.B0238.Ec tr ρ)) x) -
      (UnforcedLeray.B0238.Vc tr ρ x 0 * UnforcedLeray.Cyl.partialQ (UnforcedLeray.B0238.Ec tr ρ) x +
        UnforcedLeray.B0238.Vc tr ρ x 1 * UnforcedLeray.Cyl.partialEta
          (UnforcedLeray.B0238.Ec tr ρ) x)
    linear_combination hEc
  have hcont1 : ContinuousOn (fun p => tjW [0] (tjE tr) p) tjU :=
    (tjW_contDiffOn hE1 [0]).continuousOn
  have hcont2 : ContinuousOn (fun p => ν * (tjW [1, 1] (tjE tr) p + tjW [2, 2] (tjE tr) p) -
      (tjV tr 0 p * tjW [1] (tjE tr) p + tjV tr 1 p * tjW [2] (tjE tr) p)) tjU :=
    (continuousOn_const.mul ((tjW_contDiffOn hE1 [1, 1]).continuousOn.add
        (tjW_contDiffOn hE1 [2, 2]).continuousOn)).sub
      ((hV0.continuousOn.mul (tjW_contDiffOn hE1 [1]).continuousOn).add
        (hV1.continuousOn.mul (tjW_contDiffOn hE1 [2]).continuousOn))
  have hsub : (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) ⊆ tjU :=
    Set.prod_mono Ioi_subset_Ici_self (subset_refl _)
  have hcl : tjU ⊆ closure (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    rw [closure_prod_eq, closure_univ, closure_Ioi]
  have hEq := Set.EqOn.of_subset_closure (fun p hp => hpos p hp) hcont1 hcont2 hsub hcl
  exact ⟨hE1, hcl2, fun p hp => hEq hp⟩

end UnforcedLeray.Short.IIIa
