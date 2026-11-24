import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.TimeJets.Defs
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.SliceJetBounds
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.LocalizedCoeff.PdEcCont

/-!
# `PartIII-a:T21/2/7/2/1/1/6/23`: the vorticity-gradient jets are weighted coefficients (`TrainECoeff`)

Source: `the November 2 reference manuscript` lines 270-288, 2866-2870.
Route: `sliceJetBounds` applied to `(r, x) ↦ ∂_l E(r, x)`, with the weight `ejWeight m`.
The slice derivative `∂_l E_c(r)` is the within-strip derivative of the joint vorticity
`ecJoint` (`PdEc`), so its `n`-th joint derivative is the `(n+1)`-th derivative of `E`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The evaluation at the age-position direction `(0, dir l)`. -/
def trainEvalDir (l : Fin 2) : ((ℝ × (ℝ × ℝ)) →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.apply ℝ ℝ ((0 : ℝ), B0579.dir l)

/-- The joint spatial slope `(r, x) ↦ ∂_l E_c(r)(x)` on the strip. -/
def trainECVel {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (l : Fin 2) :
    ℝ × (ℝ × ℝ) → ℝ :=
  fun p => fderivWithin ℝ (PdEc.ecJoint tr) (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))
    p ((0 : ℝ), B0579.dir l)

theorem trainECVel_contDiffOn {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (l : Fin 2) :
    ContDiffOn ℝ ∞ (trainECVel tr l) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
  have hU : Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    prod_mono Ioi_subset_Ici_self (subset_univ _)
  have hd : ContDiffOn ℝ ∞
      (fderivWithin ℝ (PdEc.ecJoint tr) (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
      (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (PdEc.ecJoint_contDiffOn tr).fderivWithin PdEc.strip_uniqueDiff (m := ∞) (by simp)
  exact (hd.clm_apply (contDiffOn_const (c := ((0 : ℝ), B0579.dir l)))).mono hU

theorem pd_Ec_eq_trainECVel {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (l : Fin 2)
    {r : ℝ} (hr : 0 ≤ r) (x : ℝ × ℝ) :
    B0579.pd l (UnforcedLeray.B0238.Ec tr r) x = trainECVel tr l (r, x) := by
  unfold trainECVel B0579.pd
  rw [PdEc.Ec_eq_ecJoint tr hr]
  exact PdEc.fderiv_slice_apply (PdEc.ecJoint_contDiffOn tr) hr x (B0579.dir l)

theorem trainEC_fderiv_periodic {c : ℝ} {g : ℝ × ℝ → ℝ}
    (hg : ∀ z : ℝ × ℝ, g (z.1 + c, z.2) = g z) (z : ℝ × ℝ) :
    fderiv ℝ g (z.1 + c, z.2) = fderiv ℝ g z := by
  have hsh : ∀ y : ℝ × ℝ, y + ((c : ℝ), (0 : ℝ)) = (y.1 + c, y.2) := fun y => by
    ext <;> simp
  have h1 : (fun y : ℝ × ℝ => g (y + ((c : ℝ), (0 : ℝ)))) = g := by
    funext y
    rw [hsh y]
    exact hg y
  have h2 : fderiv ℝ (fun y : ℝ × ℝ => g (y + ((c : ℝ), (0 : ℝ)))) z
      = fderiv ℝ g (z + ((c : ℝ), (0 : ℝ))) := fderiv_comp_add_right ((c : ℝ), (0 : ℝ))
  rw [h1, hsh z] at h2
  exact h2.symm

theorem trainEC_Ec_periodic {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ}
    (hs : 0 ≤ s) (z : ℝ × ℝ) :
    UnforcedLeray.B0238.Ec tr s (z.1 + c, z.2) = UnforcedLeray.B0238.Ec tr s z := by
  have hv : ContDiff ℝ 1 (tr.v s) :=
    (UnforcedLeray.B0238.contDiff_Vc tr hs).of_le (by exact_mod_cast le_top)
  have hp : ∀ y : ℝ × ℝ, tr.v s (y.1 + c, y.2) = tr.v s y := fun y =>
    tr.isTrain.periodic_v s hs y
  have hg1 : ∀ y : ℝ × ℝ, (fun w : ℝ × ℝ => tr.v s w 1) (y.1 + c, y.2)
      = (fun w : ℝ × ℝ => tr.v s w 1) y := fun y => by
    simp only [hp y]
  have hg0 : ∀ y : ℝ × ℝ, (fun w : ℝ × ℝ => tr.v s w 0) (y.1 + c, y.2)
      = (fun w : ℝ × ℝ => tr.v s w 0) y := fun y => by
    simp only [hp y]
  show UnforcedLeray.Cyl.curl (tr.v s) (z.1 + c, z.2) = UnforcedLeray.Cyl.curl (tr.v s) z
  rw [UnforcedLeray.B0238.curl_eq_fderiv hv (z.1 + c, z.2),
    UnforcedLeray.B0238.curl_eq_fderiv hv z,
    trainEC_fderiv_periodic (g := fun w : ℝ × ℝ => tr.v s w 1) (c := c) hg1 z,
    trainEC_fderiv_periodic (g := fun w : ℝ × ℝ => tr.v s w 0) (c := c) hg0 z]

theorem eJet_periodic {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (i : ℕ) {r : ℝ}
    (hr : 0 < r) (l : Fin 2) (x : ℝ × ℝ) :
    eJet tr i r l (x.1 + c, x.2) = eJet tr i r l x := by
  unfold eJet
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [Ioi_mem_nhds hr] with ρ hρ
  have hρ0 : (0 : ℝ) ≤ ρ := le_of_lt (show (0 : ℝ) < ρ from hρ)
  show B0579.pd l (UnforcedLeray.B0238.Ec tr ρ) (x.1 + c, x.2)
    = B0579.pd l (UnforcedLeray.B0238.Ec tr ρ) x
  unfold B0579.pd
  rw [trainEC_fderiv_periodic (g := UnforcedLeray.B0238.Ec tr ρ) (c := c)
    (fun z => trainEC_Ec_periodic tr hρ0 z) x]

theorem eJet_eq_iter {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (i : ℕ) {r : ℝ}
    (hr : 0 < r) (l : Fin 2) (x : ℝ × ℝ) :
    eJet tr i r l x = iteratedDeriv i (fun ρ => trainECVel tr l (ρ, x)) r := by
  unfold eJet
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [Ioi_mem_nhds hr] with ρ hρ
  exact pd_Ec_eq_trainECVel tr l (le_of_lt (show (0 : ℝ) < ρ from hρ)) x

theorem trainECVel_norm_le {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (m : ℝ)
    (l : Fin 2) (n : ℕ) (S C : ℝ)
    (hC : ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
      ejWeight m x * ‖iteratedFDerivWithin ℝ (n + 1)
        (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖ ≤ C)
    (ρ : ℝ) (hρ : ρ ∈ Ioo (0 : ℝ) S) (x : ℝ × ℝ) :
    ejWeight m x * ‖iteratedFDeriv ℝ n (trainECVel tr l) (ρ, x)‖ ≤
      ‖trainEvalDir l‖ * C := by
  have hUS : Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) ⊆ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
    prod_mono Ioi_subset_Ici_self (subset_univ _)
  have hUo : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hmem : (ρ, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hρ.1, mem_univ _⟩
  have hmemS : (ρ, x) ∈ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := hUS hmem
  have hGc : ContDiffOn ℝ ∞
      (fderivWithin ℝ (PdEc.ecJoint tr) (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
      (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (PdEc.ecJoint_contDiffOn tr).fderivWithin PdEc.strip_uniqueDiff (m := ∞) (by simp)
  have hGU : ContDiffWithinAt ℝ ∞
      (fderivWithin ℝ (PdEc.ecJoint tr) (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
      (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x) :=
    (hGc.mono hUS).contDiffWithinAt hmem
  have h1 : iteratedFDeriv ℝ n (trainECVel tr l) (ρ, x)
      = iteratedFDerivWithin ℝ n (trainECVel tr l) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))
          (ρ, x) :=
    (iteratedFDerivWithin_of_isOpen n hUo hmem).symm
  have h2 : ‖iteratedFDerivWithin ℝ n (trainECVel tr l)
        (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖ ≤
      ‖trainEvalDir l‖ * ‖iteratedFDerivWithin ℝ n
        (fderivWithin ℝ (PdEc.ecJoint tr) (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
        (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖ :=
    (trainEvalDir l).norm_iteratedFDerivWithin_comp_left hGU hUo.uniqueDiffOn hmem
      (by exact_mod_cast le_top)
  have h3 : iteratedFDerivWithin ℝ n
        (fderivWithin ℝ (PdEc.ecJoint tr) (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
        (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)
      = iteratedFDerivWithin ℝ n
        (fderivWithin ℝ (PdEc.ecJoint tr) (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x) := by
    have := iteratedFDerivWithin_inter_open (𝕜 := ℝ)
      (f := fderivWithin ℝ (PdEc.ecJoint tr) (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
      (s := Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (n := n) hUo hmem
    rwa [inter_eq_right.2 hUS] at this
  have h4 : ‖iteratedFDerivWithin ℝ n
        (fderivWithin ℝ (PdEc.ecJoint tr) (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖
      = ‖iteratedFDerivWithin ℝ (n + 1) (PdEc.ecJoint tr)
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖ :=
    norm_iteratedFDerivWithin_fderivWithin PdEc.strip_uniqueDiff hmemS
  have hEq : EqOn (PdEc.ecJoint tr)
      (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
      (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := fun p hp =>
    (congrFun (PdEc.Ec_eq_ecJoint tr (Set.mem_Ici.1 hp.1)) p.2).symm
  have h5 : iteratedFDerivWithin ℝ (n + 1) (PdEc.ecJoint tr)
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)
      = iteratedFDerivWithin ℝ (n + 1)
        (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x) :=
    iteratedFDerivWithin_congr hEq hmemS (n + 1)
  have hX : ‖iteratedFDerivWithin ℝ n (trainECVel tr l)
        (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖ ≤
      ‖trainEvalDir l‖ * ‖iteratedFDerivWithin ℝ (n + 1)
        (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖ := by
    refine h2.trans ?_
    rw [h3, h4, h5]
  have hw : 0 ≤ ejWeight m x := by unfold ejWeight; positivity
  have h6 := hC ρ ⟨hρ.1.le, hρ.2.le⟩ x
  rw [h1]
  calc ejWeight m x * ‖iteratedFDerivWithin ℝ n (trainECVel tr l)
        (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖
      ≤ ejWeight m x * (‖trainEvalDir l‖ * ‖iteratedFDerivWithin ℝ (n + 1)
        (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖) :=
        mul_le_mul_of_nonneg_left hX hw
    _ = ‖trainEvalDir l‖ * (ejWeight m x * ‖iteratedFDerivWithin ℝ (n + 1)
        (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖) := by ring
    _ ≤ ‖trainEvalDir l‖ * C := mul_le_mul_of_nonneg_left h6 (norm_nonneg (trainEvalDir l))

/-- **The vorticity-gradient jets are weighted coefficients** (SP 2866-2870; `TrainSTJets`). -/
theorem trainECoeff (m : ℝ) : TrainECoeff m := by
  unfold TrainECoeff
  intro ν hν0 hν1 tr hST a b ha i
  have hpos : ∀ x : ℝ × ℝ, 0 < ejWeight m x := fun x =>
    Real.rpow_pos_of_pos (by positivity) _
  have hVb : ∀ l : Fin 2, ∀ (n : ℕ) (S : ℝ), ∃ C : ℝ, ∀ ρ ∈ Ioo (0 : ℝ) S, ∀ x : ℝ × ℝ,
      ejWeight m x * ‖iteratedFDeriv ℝ n (trainECVel tr l) (ρ, x)‖ ≤ C := by
    intro l n S
    obtain ⟨C, hC⟩ := hST (max S 0) (le_max_right S 0) n
    refine ⟨‖trainEvalDir l‖ * C, fun ρ hρ x => ?_⟩
    have hρS : ρ ∈ Ioo (0 : ℝ) (max S 0) := ⟨hρ.1, hρ.2.trans_le (le_max_left S 0)⟩
    exact trainECVel_norm_le tr m l n (max S 0) C (fun ρ hρ x => (hC ρ hρ x).2) ρ hρS x
  have key := fun l : Fin 2 => sliceJetBounds (trainECVel tr l) (ejWeight m) hpos
    (trainECVel_contDiffOn tr l) (hVb l) a b ha i
  have hGr : ∀ r ∈ Ioo a b, ∀ l : Fin 2,
      (fun x : ℝ × ℝ => eJet tr i r l x)
        = (fun x => iteratedDeriv i (fun ρ => trainECVel tr l (ρ, x)) r) := by
    intro r hr l
    funext x
    exact eJet_eq_iter tr i (lt_of_le_of_lt ha hr.1) l x
  refine ⟨⟨fun r hr l => ⟨?_, fun x => ?_⟩, fun w l r hr => ?_⟩, fun l => ?_⟩
  · show ContDiff ℝ ∞ (fun x : ℝ × ℝ => eJet tr i r l x)
    rw [hGr r hr l]
    exact (key l).1 r hr
  · show eJet tr i r l (x.1 + ν ^ (-2 : ℝ), x.2) = eJet tr i r l x
    exact eJet_periodic tr i (lt_of_le_of_lt ha hr.1) l x
  · have hk := (key l).2.1 w r hr
    refine ⟨?_, ?_⟩
    · obtain ⟨C, hC⟩ := hk.1
      refine ⟨C, fun x => ?_⟩
      have := hC x
      rw [← hGr r hr l] at this
      exact this
    · intro ε hε
      filter_upwards [hk.2 ε hε, self_mem_nhdsWithin] with r' hr' hr'mem x
      have e' := hGr r' hr'mem l
      have e := hGr r hr l
      have := hr' x
      rw [← e', ← e] at this
      exact this
  · intro r hr ε hε
    have hr0 : 0 < r := lt_of_le_of_lt ha hr.1
    have hmemI : ∀ᶠ r' in 𝓝[Ioo a b \ {r}] r, r' ∈ Ioo a b :=
      eventually_mem_nhdsWithin.mono (fun r' h => h.1)
    filter_upwards [(key l).2.2 r hr ε hε, hmemI] with r' hr' hr'I x
    have hr'0 : 0 < r' := lt_of_le_of_lt ha hr'I.1
    rw [eJet_eq_iter tr i hr'0 l x, eJet_eq_iter tr i hr0 l x, eJet_eq_iter tr (i + 1) hr0 l x]
    exact hr' x

end UnforcedLeray.Short.IIIa
