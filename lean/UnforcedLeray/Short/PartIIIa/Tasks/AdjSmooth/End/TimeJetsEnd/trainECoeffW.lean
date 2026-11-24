import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.End.TimeJetsEnd.trainVCoeffW.SliceJetBoundsW
import UnforcedLeray.Short.PartIIIa.Tasks.AdjSmooth.Interior.TimeJets.TrainECoeff

/-!
# `PartIII-a:T21/2/7/2/1/2/1/2/7`: the one-sided vorticity-gradient jets are weighted coefficients

Source: `the November 2 reference manuscript` lines 270-288, 2866-2870, 3052-3061.
Route: `sliceJetBoundsW` applied to `(r, x) ↦ ∂_l E(r, x)` (`trainECVel`) with the weight
`ejWeight m`; the bound is the second clause of `TrainSTJets`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- One-sided derivative bound for the slope `trainECVel` on the closed strip. -/
theorem trainECVel_norm_leW {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (m : ℝ)
    (l : Fin 2) (n : ℕ) (S C : ℝ)
    (hC : ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
      ejWeight m x * ‖iteratedFDerivWithin ℝ (n + 1)
        (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖ ≤ C)
    (ρ : ℝ) (hρ : ρ ∈ Icc (0 : ℝ) S) (x : ℝ × ℝ) :
    ejWeight m x * ‖iteratedFDerivWithin ℝ n (trainECVel tr l)
      (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖ ≤ ‖trainEvalDir l‖ * C := by
  have hmemS : (ρ, x) ∈ Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hρ.1, mem_univ _⟩
  have hGc : ContDiffOn ℝ ∞
      (fderivWithin ℝ (PdEc.ecJoint tr) (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
      (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) :=
    (PdEc.ecJoint_contDiffOn tr).fderivWithin PdEc.strip_uniqueDiff (m := ∞) (by simp)
  have h2 := (trainEvalDir l).norm_iteratedFDerivWithin_comp_left (n := n) (hGc (ρ, x) hmemS)
    PdEc.strip_uniqueDiff hmemS (by exact_mod_cast le_top)
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
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖ ≤
      ‖trainEvalDir l‖ * ‖iteratedFDerivWithin ℝ (n + 1)
        (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖ := by
    refine h2.trans ?_
    rw [h4, h5]
  have hw : 0 ≤ ejWeight m x := by unfold ejWeight; positivity
  have h6 := hC ρ hρ x
  calc ejWeight m x * ‖iteratedFDerivWithin ℝ n (trainECVel tr l)
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖
      ≤ ejWeight m x * (‖trainEvalDir l‖ * ‖iteratedFDerivWithin ℝ (n + 1)
        (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖) :=
        mul_le_mul_of_nonneg_left hX hw
    _ = ‖trainEvalDir l‖ * (ejWeight m x * ‖iteratedFDerivWithin ℝ (n + 1)
        (fun p : ℝ × (ℝ × ℝ) => UnforcedLeray.B0238.Ec tr p.1 p.2)
        (Ici (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) (ρ, x)‖) := by ring
    _ ≤ ‖trainEvalDir l‖ * C := mul_le_mul_of_nonneg_left h6 (norm_nonneg (trainEvalDir l))

/-- The one-sided vorticity jet is the one-sided age jet of `trainECVel`, for `r ≥ 0`. -/
theorem eJetW_eq_iter {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (i : ℕ) {r : ℝ}
    (hr : 0 ≤ r) (l : Fin 2) (x : ℝ × ℝ) :
    eJetW tr i r l x = iteratedDerivWithin i (fun ρ => trainECVel tr l (ρ, x)) (Ici 0) r := by
  unfold eJetW
  exact iteratedDerivWithin_congr (fun ρ hρ => pd_Ec_eq_trainECVel tr l hρ x)
    (show r ∈ Ici (0 : ℝ) from hr)

/-- **The one-sided vorticity-gradient jets are weighted coefficients on `[a, b)`**
(SP 2866-2870, 3060). -/
theorem trainECoeffW : ∀ m : ℝ, TrainECoeffW m := by
  intro m
  unfold TrainECoeffW
  intro ν hν0 hν1 tr hST a b ha i
  have hpos : ∀ x : ℝ × ℝ, 0 < ejWeight m x := fun x =>
    Real.rpow_pos_of_pos (by positivity) _
  have hVb : ∀ l : Fin 2, ∀ (n : ℕ) (S : ℝ), ∃ C : ℝ, ∀ ρ ∈ Icc (0 : ℝ) S, ∀ x : ℝ × ℝ,
      ejWeight m x * ‖iteratedFDerivWithin ℝ n (trainECVel tr l)
        (Ici 0 ×ˢ univ) (ρ, x)‖ ≤ C := by
    intro l n S
    obtain ⟨C, hC⟩ := hST (max S 0) (le_max_right S 0) n
    refine ⟨‖trainEvalDir l‖ * C, fun ρ hρ x => ?_⟩
    have hρS : ρ ∈ Icc (0 : ℝ) (max S 0) := ⟨hρ.1, hρ.2.trans (le_max_left S 0)⟩
    exact trainECVel_norm_leW tr m l n (max S 0) C (fun ρ hρ x => (hC ρ hρ x).2) ρ hρS x
  have hU : ∀ l : Fin 2, ContDiffOn ℝ ∞ (trainECVel tr l) (Ici 0 ×ˢ univ) := fun l =>
    ((PdEc.ecJoint_contDiffOn tr).fderivWithin PdEc.strip_uniqueDiff (m := ∞) (by simp)).clm_apply
      (contDiffOn_const (c := ((0 : ℝ), B0579.dir l)))
  have key := fun l : Fin 2 => sliceJetBoundsW (trainECVel tr l) (ejWeight m) hpos (hU l)
    (hVb l) a b ha i
  have hGr : ∀ r ∈ Ico a b, ∀ l : Fin 2,
      (fun x : ℝ × ℝ => eJetW tr i r l x)
        = (fun x => iteratedDerivWithin i (fun ρ => trainECVel tr l (ρ, x)) (Ici 0) r) := by
    intro r hr l
    funext x
    exact eJetW_eq_iter tr i (ha.trans hr.1) l x
  have hper : ∀ r ∈ Ico a b, ∀ l : Fin 2, ∀ x : ℝ × ℝ,
      eJetW tr i r l (x.1 + ν ^ (-2 : ℝ), x.2) = eJetW tr i r l x := by
    intro r hr l x
    unfold eJetW
    refine iteratedDerivWithin_congr (fun ρ hρ => ?_) (show r ∈ Ici (0 : ℝ) from ha.trans hr.1)
    have hρ0 : (0 : ℝ) ≤ ρ := hρ
    show B0579.pd l (UnforcedLeray.B0238.Ec tr ρ) (x.1 + ν ^ (-2 : ℝ), x.2)
      = B0579.pd l (UnforcedLeray.B0238.Ec tr ρ) x
    unfold B0579.pd
    rw [trainEC_fderiv_periodic (g := UnforcedLeray.B0238.Ec tr ρ) (c := ν ^ (-2 : ℝ))
      (fun z => trainEC_Ec_periodic tr hρ0 z) x]
  refine ⟨⟨fun r hr l => ⟨?_, fun x => hper r hr l x⟩, fun w l r hr => ?_⟩, fun l => ?_⟩
  · show ContDiff ℝ ∞ (fun x : ℝ × ℝ => eJetW tr i r l x)
    rw [hGr r hr l]
    exact (key l).1 r hr
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
    have hmemI : ∀ᶠ r' in 𝓝[Ico a b \ {r}] r, r' ∈ Ico a b :=
      eventually_mem_nhdsWithin.mono (fun r' h => h.1)
    filter_upwards [(key l).2.2 r hr ε hε, hmemI] with r' hr' hr'I x
    rw [eJetW_eq_iter tr i (ha.trans hr'I.1) l x, eJetW_eq_iter tr i (ha.trans hr.1) l x,
      eJetW_eq_iter tr (i + 1) (ha.trans hr.1) l x]
    exact hr' x

end UnforcedLeray.Short.IIIa
