import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayOf
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayPotDecay
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayPotSmooth
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayPotPoisson
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayBoundedDeriv
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_1.LerayForceDeriv

/-!
# The Leray field `W = F - ∇u` (`LerayFieldProps`)

Source `the November 2 reference manuscript` 1655-1656, 1676 (`W = P₀ F = F - ∇u`,
`u = lerayPot c F`).  Components of `∇u` are `lerayPot` of the force fields `∂_v F`
(`LerayPotSmooth`), so all bounds on `W` come from the leaves `LerayPotSmooth`, `LerayPotDecay`,
`LerayPotPoisson`, `BoundedDerivBand`, `ForceFieldDeriv`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

/-- The two coordinate directions `(0,(1,0))` (for `∂_q`) and `(0,(0,1))` (for `∂_η`) of `Chart`. -/
def lfpDir (i : Fin 2) : Chart :=
  ![((0 : ℝ), ((1 : ℝ), (0 : ℝ))), ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))] i

lemma lfp_abs_sub (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b]

lemma lfp_fderiv_periodic {c : ℝ} {f : Chart → ℝ}
    (hf : ∀ s q η, f (s, (q + c, η)) = f (s, (q, η))) (v : Chart) (s q η : ℝ) :
    fderiv ℝ f (s, (q + c, η)) v = fderiv ℝ f (s, (q, η)) v := by
  have hfun : (fun z : Chart => f (z + (0, (c, (0 : ℝ))))) = fun z => f z := by
    funext z
    obtain ⟨s', q', η'⟩ := z
    simp only [Prod.mk_add_mk, add_zero]
    exact hf s' q' η'
  have hshift : ∀ x : Chart, fderiv ℝ f (x + (0, (c, (0 : ℝ)))) = fderiv ℝ f x := by
    intro x
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (0, (c, (0 : ℝ))) (x := x)
    rw [hfun] at h
    exact h.symm
  have hp : ((s, (q + c, η)) : Chart) = (s, (q, η)) + (0, (c, (0 : ℝ))) := by
    simp
  rw [hp, hshift]

lemma lfp_dfDv_periodic {c : ℝ} {F : Chart → Fin 2 → ℝ}
    (hFp : ∀ s q η, F (s, (q + c, η)) = F (s, (q, η))) (v : Chart) :
    ∀ s q η, dfDv F v (s, (q + c, η)) = dfDv F v (s, (q, η)) := by
  intro s q η
  funext j
  exact lfp_fderiv_periodic (f := fun p => F p j) (c := c)
    (fun s' q' η' => congrFun (hFp s' q' η') j) v s q η

lemma lfp_dfDv_band {F : Chart → Fin 2 → ℝ} {s0 s1 : ℝ}
    (hFb : ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1) (v : Chart) :
    ∀ q, dfDv F v q ≠ 0 → q.1 ∈ Icc s0 s1 := by
  intro q hq
  by_contra hs
  apply hq
  funext j
  have hb : ∀ p : Chart, (fun p' => F p' j) p ≠ 0 → p.1 ∈ Icc s0 s1 :=
    fun p hp => hFb p (fun h0 => hp (by simp [h0]))
  have hz : fderiv ℝ (fun p' => F p' j) q = 0 :=
    fderiv_eq_zero_of_band (u := fun p' => F p' j) hb hs
  show fderiv ℝ (fun p' => F p' j) q v = 0
  rw [hz]
  simp

lemma lfp_dQ_sub' (A B : Chart → ℝ) (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (q : Chart) :
    UnforcedLeray.Axi.dQ (fun q' => A q' - B q') q =
      UnforcedLeray.Axi.dQ A q - UnforcedLeray.Axi.dQ B q := by
  unfold UnforcedLeray.Axi.dQ
  have hs : fderiv ℝ (fun q' => A q' - B q') q = fderiv ℝ A q - fderiv ℝ B q :=
    fderiv_sub (hA q) (hB q)
  simp only [hs, ContinuousLinearMap.sub_apply]

lemma lfp_dEta_sub' (A B : Chart → ℝ) (hA : Differentiable ℝ A) (hB : Differentiable ℝ B)
    (q : Chart) :
    UnforcedLeray.Axi.dEta (fun q' => A q' - B q') q =
      UnforcedLeray.Axi.dEta A q - UnforcedLeray.Axi.dEta B q := by
  unfold UnforcedLeray.Axi.dEta
  have hs : fderiv ℝ (fun q' => A q' - B q') q = fderiv ℝ A q - fderiv ℝ B q :=
    fderiv_sub (hA q) (hB q)
  simp only [hs, ContinuousLinearMap.sub_apply]

/-- **The Leray field** `W = F - ∇u`: smooth, periodic, band supported in `s`, all derivatives
bounded, exponentially decaying in `η`, divergence free (`LerayFieldProps`). -/
theorem lerayFieldProps : LerayFieldProps := by
  intro c hc F hF
  have hF' := hF
  obtain ⟨hFs, hFp, s0, s1, L, hs0, hFb⟩ := hF'
  have hbF : ∀ p : Chart, F p ≠ 0 → p.1 ∈ Icc s0 s1 := fun p hp => (hFb p hp).1
  have hGs : ∀ i : Fin 2, IsForceField c (dfDv F (lfpDir i)) :=
    fun i => forceFieldDeriv c F hF (lfpDir i)
  have hflat : ∀ (i : Fin 2) (p : Chart),
      flatGrad (lerayPot c F) p i = lerayPot c (dfDv F (lfpDir i)) p := by
    intro i p
    fin_cases i
    · exact (lerayPotSmooth c hc F hF).2.2 p (lfpDir 0)
    · exact (lerayPotSmooth c hc F hF).2.2 p (lfpDir 1)
  have hL : ∀ (i : Fin 2) (p : Chart),
      lerayField c F p i = F p i - lerayPot c (dfDv F (lfpDir i)) p := by
    intro i p
    show F p i - flatGrad (lerayPot c F) p i = F p i - lerayPot c (dfDv F (lfpDir i)) p
    rw [hflat i p]
  have hperL : ∀ i : Fin 2, ∀ s q η : ℝ,
      lerayPot c (dfDv F (lfpDir i)) (s, (q + c, η)) =
        lerayPot c (dfDv F (lfpDir i)) (s, (q, η)) :=
    fun i => lerayPot_periodic (lfp_dfDv_periodic hFp (lfpDir i))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness
    intro i
    have e : (fun p : Chart => lerayField c F p i) =
        fun p => F p i - lerayPot c (dfDv F (lfpDir i)) p := funext (hL i)
    rw [e]
    exact (hFs i).sub (lerayPotSmooth c hc _ (hGs i)).1
  · -- periodicity in q
    intro s q η
    funext i
    rw [hL i (s, (q + c, η)), hL i (s, (q, η)), congrFun (hFp s q η) i, hperL i s q η]
  · -- s-band
    refine ⟨s0, s1, hs0, fun p hp => ?_⟩
    by_contra hs
    apply hp
    funext i
    show lerayField c F p i = 0
    have h1 : F p i = 0 := by
      by_contra h
      exact hs (hbF p (fun h0 => h (by simp [h0])))
    have h2 : lerayPot c (dfDv F (lfpDir i)) p = 0 := by
      by_contra h
      exact hs (lerayPot_band (lfp_dfDv_band hbF (lfpDir i)) p h)
    simp [hL i p, h1, h2]
  · -- bounded derivatives
    intro i n
    obtain ⟨C1, hC1⟩ := boundedDerivBand c hc (fun p => F p i) (hFs i)
      (fun s q η => congrFun (hFp s q η) i)
      ⟨s0, s1, L, fun p hp => hFb p (fun h0 => hp (by simp [h0]))⟩ n
    obtain ⟨C2, hC2⟩ := (lerayPotSmooth c hc _ (hGs i)).2.1 n
    refine ⟨C1 + C2, fun p => ?_⟩
    have hAd : ContDiffAt ℝ n (fun p : Chart => F p i) p :=
      ((hFs i).of_le (by simp)).contDiffAt
    have hBd : ContDiffAt ℝ n (fun p : Chart => lerayPot c (dfDv F (lfpDir i)) p) p :=
      ((lerayPotSmooth c hc _ (hGs i)).1.of_le (by simp)).contDiffAt
    rw [show (fun p : Chart => lerayField c F p i) =
        fun p => F p i - lerayPot c (dfDv F (lfpDir i)) p from funext (hL i)]
    rw [show (fun p : Chart => F p i - lerayPot c (dfDv F (lfpDir i)) p) =
        (fun p : Chart => F p i) - (fun p : Chart => lerayPot c (dfDv F (lfpDir i)) p) from rfl]
    rw [iteratedFDeriv_sub_apply hAd hBd]
    exact (norm_sub_le _ _).trans (add_le_add (hC1 p) (hC2 p))
  · -- exponential decay in eta
    obtain ⟨Cd, κ, hκ, hdec⟩ := lerayPotDecay c hc F hF
    have hMi : ∀ i : Fin 2, ∃ M : ℝ, ∀ p : Chart, |F p i| ≤ M := by
      intro i
      obtain ⟨M, hM⟩ := boundedDerivBand c hc (fun p => F p i) (hFs i)
        (fun s q η => congrFun (hFp s q η) i)
        ⟨s0, s1, L, fun p hp => hFb p (fun h0 => hp (by simp [h0]))⟩ 0
      refine ⟨M, fun p => ?_⟩
      have h := hM p
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
      exact h
    obtain ⟨M0, h0⟩ := hMi 0
    obtain ⟨M1, h1⟩ := hMi 1
    have hM0 : 0 ≤ |M0| + |M1| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hMall : ∀ (p : Chart) (i : Fin 2), |F p i| ≤ |M0| + |M1| := by
      intro p i
      fin_cases i
      · exact (h0 p).trans (by linarith [le_abs_self M0, abs_nonneg M1])
      · exact (h1 p).trans (by linarith [le_abs_self M1, abs_nonneg M0])
    have hFz : ∀ p : Chart, |p.2.2| > L → ∀ i : Fin 2, F p i = 0 := by
      intro p hp i
      by_contra h
      exact absurd (hFb p (fun h0 => h (by simp [h0]))).2 (not_le.2 hp)
    have hFdec : ∀ (p : Chart) (i : Fin 2),
        |F p i| ≤ ((|M0| + |M1|) * Real.exp (κ * L)) * Real.exp (-(κ * |p.2.2|)) := by
      intro p i
      by_cases hη : |p.2.2| ≤ L
      · have hk : κ * |p.2.2| ≤ κ * L := mul_le_mul_of_nonneg_left hη hκ.le
        have h1' : 1 ≤ Real.exp (κ * L) * Real.exp (-(κ * |p.2.2|)) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          linarith
        calc |F p i| ≤ |M0| + |M1| := hMall p i
          _ = (|M0| + |M1|) * 1 := (mul_one _).symm
          _ ≤ (|M0| + |M1|) * (Real.exp (κ * L) * Real.exp (-(κ * |p.2.2|))) :=
              mul_le_mul_of_nonneg_left h1' hM0
          _ = ((|M0| + |M1|) * Real.exp (κ * L)) * Real.exp (-(κ * |p.2.2|)) := by ring
      · rw [hFz p (not_le.1 hη) i, abs_zero]
        exact mul_nonneg (mul_nonneg hM0 (Real.exp_nonneg _)) (Real.exp_nonneg _)
    refine ⟨(|M0| + |M1|) * Real.exp (κ * L) + Cd, κ, hκ, fun p i => ?_⟩
    show |F p i - flatGrad (lerayPot c F) p i| ≤ _
    calc |F p i - flatGrad (lerayPot c F) p i| ≤ |F p i| + |flatGrad (lerayPot c F) p i| :=
          lfp_abs_sub _ _
      _ ≤ ((|M0| + |M1|) * Real.exp (κ * L)) * Real.exp (-(κ * |p.2.2|)) +
            Cd * Real.exp (-(κ * |p.2.2|)) :=
          add_le_add (hFdec p i) (flatGrad_decay hdec p i)
      _ = ((|M0| + |M1|) * Real.exp (κ * L) + Cd) * Real.exp (-(κ * |p.2.2|)) := by ring
  · -- divergence free
    intro p
    have hdQu : UnforcedLeray.Axi.dQ (lerayPot c F) = lerayPot c (dfDv F (lfpDir 0)) :=
      funext fun q => (lerayPotSmooth c hc F hF).2.2 q (lfpDir 0)
    have hdEu : UnforcedLeray.Axi.dEta (lerayPot c F) = lerayPot c (dfDv F (lfpDir 1)) :=
      funext fun q => (lerayPotSmooth c hc F hF).2.2 q (lfpDir 1)
    have hP := lerayPotPoisson c hc F hF p
    rw [hdQu, hdEu] at hP
    have e0 : (fun q : Chart => lerayField c F q 0) =
        fun q => F q 0 - lerayPot c (dfDv F (lfpDir 0)) q := funext (hL 0)
    have e1 : (fun q : Chart => lerayField c F q 1) =
        fun q => F q 1 - lerayPot c (dfDv F (lfpDir 1)) q := funext (hL 1)
    have hd0 : Differentiable ℝ (fun q : Chart => F q 0) := (hFs 0).differentiable (by simp)
    have hd1 : Differentiable ℝ (fun q : Chart => F q 1) := (hFs 1).differentiable (by simp)
    have hg0 : Differentiable ℝ (lerayPot c (dfDv F (lfpDir 0))) :=
      (lerayPotSmooth c hc _ (hGs 0)).1.differentiable (by simp)
    have hg1 : Differentiable ℝ (lerayPot c (dfDv F (lfpDir 1))) :=
      (lerayPotSmooth c hc _ (hGs 1)).1.differentiable (by simp)
    unfold flatDiv at hP ⊢
    rw [e0, e1, lfp_dQ_sub' _ _ hd0 hg0 p, lfp_dEta_sub' _ _ hd1 hg1 p]
    linarith

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
