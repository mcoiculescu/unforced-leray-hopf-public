import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_3_1
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_3.LinAdjDuality.CutProps
import UnforcedLeray.Lib.Cylinder.IBP

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff Interval

namespace UnforcedLeray.Short.IIIa

namespace CutIBPAux

/-! ### Elementary facts -/

lemma re_conj_eq (a b : ℂ) : ((starRingEnd ℂ) a * b).re = inner ℝ a b := by
  rw [Complex.inner, mul_comm]

lemma ladCut_zero' {R : ℝ} (hR : 0 < R) {x : ℝ × ℝ} (hx : 2 * R ^ 2 ≤ x.2 ^ 2) :
    ladCut R x = 0 := by
  obtain ⟨K, _, h⟩ := ladCutProps
  exact (h R hR).2.2.2.1 x hx

lemma contDiff_ladCut (R : ℝ) : ContDiff ℝ ∞ (ladCut R) := by
  unfold ladCut
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

lemma contDiff_Aw (R m : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ × ℝ => ladCut R y ^ 2 * B0579.jb y ^ (-m)) := by
  have hj : ContDiff ℝ ∞ (fun y : ℝ × ℝ => B0579.jb y) := by
    unfold B0579.jb
    fun_prop
  exact ((contDiff_ladCut R).pow 2).mul (hj.rpow_const_of_ne (fun y => (B0579.jb_pos y).ne'))

lemma contDiff_pdCx' {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (k : Fin 2) :
    ContDiff ℝ ∞ (pdCx k f) := by
  unfold pdCx
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma contDiff_re_conj_mul {u F : ℝ × ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun y => ((starRingEnd ℂ) (u y) * F y).re) := by
  have hc : ContDiff ℝ ∞ (fun y => (starRingEnd ℂ) (u y)) := Complex.conjCLE.contDiff.comp hu
  exact Complex.reCLM.contDiff.comp (hc.mul hF)

lemma pdCx_periodic_aux (k : Fin 2) (Φ : ℝ × ℝ → ℂ) {c : ℝ}
    (hper : ∀ x : ℝ × ℝ, Φ (x.1 + c, x.2) = Φ x) :
    ∀ x : ℝ × ℝ, pdCx k Φ (x.1 + c, x.2) = pdCx k Φ x := by
  intro x
  have hfun : (fun y : ℝ × ℝ => Φ (y + ((c, 0) : ℝ × ℝ))) = Φ := by
    funext y
    have hy : y + ((c, 0) : ℝ × ℝ) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hper y
  have h1 : fderiv ℝ (fun y : ℝ × ℝ => Φ (y + ((c, 0) : ℝ × ℝ))) x
      = fderiv ℝ Φ (x + ((c, 0) : ℝ × ℝ)) := fderiv_comp_add_right _
  rw [hfun] at h1
  have hx : (x.1 + c, x.2) = x + ((c, 0) : ℝ × ℝ) := by ext <;> simp
  unfold pdCx
  rw [hx, ← h1]

lemma integrableOn_cell_strict {c R : ℝ} (hR : 0 < R) {g : ℝ × ℝ → ℝ} (hg : Continuous g)
    (h0 : ∀ x : ℝ × ℝ, 2 * R ^ 2 < x.2 ^ 2 → g x = 0) :
    IntegrableOn g (B0579.cell c) := by
  refine B0579.integrableOn_cell_of_continuous hg (B0579.isCompact_box c (2 * R)) ?_
  intro x hx hxK
  apply h0
  by_contra hcon
  push Not at hcon
  apply hxK
  apply B0579.mem_box_of_mem_cell hx
  nlinarith [sq_abs x.2, abs_nonneg x.2]

lemma cell_eq (c : ℝ) : UnforcedLeray.Cyl.cell c = B0579.cell c := by
  unfold UnforcedLeray.Cyl.cell B0579.cell
  rw [neg_div]

lemma continuous_pd {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ ∞ H) (k : Fin 2) :
    Continuous (B0579.pd k H) := by
  unfold B0579.pd
  exact (hH.continuous_fderiv (by simp)).clm_apply continuous_const

lemma pd_eq_zero_of_ev {H : ℝ × ℝ → ℝ} {y : ℝ × ℝ} (k : Fin 2)
    (h : H =ᶠ[𝓝 y] fun _ => 0) : B0579.pd k H y = 0 := by
  unfold B0579.pd
  rw [h.fderiv_eq]
  simp

lemma ev_zero_Aw {R m : ℝ} (hR : 0 < R) {y : ℝ × ℝ} (hy : 2 * R ^ 2 < y.2 ^ 2) :
    (fun z : ℝ × ℝ => ladCut R z ^ 2 * B0579.jb z ^ (-m)) =ᶠ[𝓝 y] fun _ => 0 := by
  have hU : IsOpen {z : ℝ × ℝ | 2 * R ^ 2 < z.2 ^ 2} :=
    isOpen_lt continuous_const (by fun_prop)
  filter_upwards [hU.mem_nhds hy] with z hz
  have hz' : 2 * R ^ 2 < z.2 ^ 2 := hz
  simp [ladCut_zero' hR hz'.le]

/-! ### The weighted real part and its derivative -/

/-- `χ_R² ⟨x⟩^{-2m} Re(conj(∂_kΦ) F)`. -/
def cutG (R m : ℝ) (Φ F : ℝ × ℝ → ℂ) (k : Fin 2) (y : ℝ × ℝ) : ℝ :=
  (ladCut R y ^ 2 * B0579.jb y ^ (-m)) * ((starRingEnd ℂ) (pdCx k Φ y) * F y).re

lemma contDiff_cutG {R m : ℝ} {Φ F : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hF : ContDiff ℝ ∞ F)
    (k : Fin 2) : ContDiff ℝ ∞ (cutG R m Φ F k) :=
  (contDiff_Aw R m).mul (contDiff_re_conj_mul (contDiff_pdCx' hΦ k) hF)

lemma pd_re_conj_mul {u F : ℝ × ℝ → ℂ} (hu : ContDiff ℝ ∞ u) (hF : ContDiff ℝ ∞ F)
    (k : Fin 2) (x : ℝ × ℝ) :
    B0579.pd k (fun y => ((starRingEnd ℂ) (u y) * F y).re) x =
      ((starRingEnd ℂ) (pdCx k u x) * F x).re + ((starRingEnd ℂ) (u x) * pdCx k F x).re := by
  have hfun : (fun y => ((starRingEnd ℂ) (u y) * F y).re) = fun y => inner ℝ (u y) (F y) :=
    funext fun y => re_conj_eq _ _
  rw [hfun]
  have hdu : DifferentiableAt ℝ u x := (hu.differentiable (by simp)) x
  have hdF : DifferentiableAt ℝ F x := (hF.differentiable (by simp)) x
  have h := hdu.hasFDerivAt.inner ℝ hdF.hasFDerivAt
  unfold B0579.pd
  rw [h.fderiv, re_conj_eq, re_conj_eq]
  simp only [fderivInnerCLM_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    pdCx]
  rw [add_comm]

lemma pd_cutG {R m : ℝ} {Φ F : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hF : ContDiff ℝ ∞ F)
    (k : Fin 2) (x : ℝ × ℝ) :
    B0579.pd k (cutG R m Φ F k) x =
      B0579.pd k (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
          ((starRingEnd ℂ) (pdCx k Φ x) * F x).re +
        (ladCut R x ^ 2 * B0579.jb x ^ (-m)) *
          (((starRingEnd ℂ) (pdCx k (pdCx k Φ) x) * F x).re +
            ((starRingEnd ℂ) (pdCx k Φ x) * pdCx k F x).re) := by
  have hu : ContDiff ℝ ∞ (pdCx k Φ) := contDiff_pdCx' hΦ k
  unfold cutG
  rw [B0579.pd_mul ((contDiff_Aw R m).differentiable (by simp))
    ((contDiff_re_conj_mul hu hF).differentiable (by simp)) k x,
    pd_re_conj_mul hu hF k x]

lemma cutG_ev_zero {R m : ℝ} (hR : 0 < R) {Φ F : ℝ × ℝ → ℂ} (k : Fin 2) {y : ℝ × ℝ}
    (hy : 2 * R ^ 2 < y.2 ^ 2) : cutG R m Φ F k =ᶠ[𝓝 y] fun _ => 0 := by
  filter_upwards [ev_zero_Aw (m := m) hR hy] with z hz
  simp [cutG, hz]

/-! ### The integration by parts in each direction -/

lemma slice_q {H : ℝ × ℝ → ℝ} (hH : Differentiable ℝ H) (q η : ℝ) :
    HasDerivAt (fun q' => H (q', η)) (B0579.pd 0 H (q, η)) q := by
  have hl : HasDerivAt (fun q' : ℝ => ((q', η) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) q :=
    (hasDerivAt_id q).prodMk (hasDerivAt_const q η)
  have h := (hH (q, η)).hasFDerivAt.comp_hasDerivAt q hl
  have e : B0579.pd 0 H (q, η) = fderiv ℝ H (q, η) ((1 : ℝ), (0 : ℝ)) := by
    unfold B0579.pd
    simp [B0579.dir]
  rw [e]
  exact h

lemma slice_eta {H : ℝ × ℝ → ℝ} (hH : Differentiable ℝ H) (q η : ℝ) :
    HasDerivAt (fun η' => H (q, η')) (B0579.pd 1 H (q, η)) η := by
  have hl : HasDerivAt (fun η' : ℝ => ((q, η') : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) η :=
    (hasDerivAt_const η q).prodMk (hasDerivAt_id η)
  have h := (hH (q, η)).hasFDerivAt.comp_hasDerivAt η hl
  have e : B0579.pd 1 H (q, η) = fderiv ℝ H (q, η) ((0 : ℝ), (1 : ℝ)) := by
    unfold B0579.pd
    simp [B0579.dir]
  rw [e]
  exact h

lemma ibp_q {c R m : ℝ} (hc : 0 < c) (hR : 0 < R) {Φ F : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (hF : ContDiff ℝ ∞ F) (hΦper : ∀ x : ℝ × ℝ, Φ (x.1 + c, x.2) = Φ x)
    (hFper : ∀ x : ℝ × ℝ, F (x.1 + c, x.2) = F x) :
    ∫ x in B0579.cell c, B0579.pd 0 (cutG R m Φ F 0) x = 0 := by
  have hG : Differentiable ℝ (cutG R m Φ F 0) := (contDiff_cutG hΦ hF 0).differentiable (by simp)
  have hi : IntegrableOn (B0579.pd 0 (cutG R m Φ F 0)) (UnforcedLeray.Cyl.cell c) := by
    rw [cell_eq c]
    exact integrableOn_cell_strict hR (continuous_pd (contDiff_cutG hΦ hF 0) 0)
      (fun x hx => pd_eq_zero_of_ev 0 (cutG_ev_zero hR 0 hx))
  have key := UnforcedLeray.Cyl.integral_cell_deriv_q hc (F := cutG R m Φ F 0)
    (F' := B0579.pd 0 (cutG R m Φ F 0)) (fun q η => slice_q hG q η) hi
  have hseam : ∀ η : ℝ, cutG R m Φ F 0 (c / 2, η) - cutG R m Φ F 0 (-c / 2, η) = 0 := by
    intro η
    have hA : ladCut R (c / 2, η) ^ 2 * B0579.jb (c / 2, η) ^ (-m) =
        ladCut R (-c / 2, η) ^ 2 * B0579.jb (-c / 2, η) ^ (-m) := by
      simp [B0579.jb, ladCut, neg_div]
    have hu : pdCx 0 Φ (c / 2, η) = pdCx 0 Φ (-c / 2, η) := by
      have h := pdCx_periodic_aux 0 Φ hΦper (-c / 2, η)
      have e : -c / 2 + c = c / 2 := by ring
      dsimp only at h
      rw [e] at h
      exact h
    have hf : F (c / 2, η) = F (-c / 2, η) := by
      have h := hFper (-c / 2, η)
      have e : -c / 2 + c = c / 2 := by ring
      dsimp only at h
      rw [e] at h
      exact h
    simp only [cutG, hA, hu, hf, sub_self]
  simp only [hseam, integral_zero] at key
  rw [cell_eq c] at key
  exact key

lemma ibp_eta {c R m : ℝ} (hR : 0 < R) {Φ F : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (hF : ContDiff ℝ ∞ F) :
    ∫ x in B0579.cell c, B0579.pd 1 (cutG R m Φ F 1) x = 0 := by
  have hG : Differentiable ℝ (cutG R m Φ F 1) := (contDiff_cutG hΦ hF 1).differentiable (by simp)
  have hi : IntegrableOn (B0579.pd 1 (cutG R m Φ F 1)) (UnforcedLeray.Cyl.cell c) := by
    rw [cell_eq c]
    exact integrableOn_cell_strict hR (continuous_pd (contDiff_cutG hΦ hF 1) 1)
      (fun x hx => pd_eq_zero_of_ev 1 (cutG_ev_zero hR 1 hx))
  have hF' : IntegrableOn (cutG R m Φ F 1) (UnforcedLeray.Cyl.cell c) := by
    rw [cell_eq c]
    exact integrableOn_cell_strict hR (contDiff_cutG hΦ hF 1).continuous
      (fun x hx => by simp [cutG, ladCut_zero' hR hx.le])
  have key := UnforcedLeray.Cyl.integral_cell_deriv_eta (F := cutG R m Φ F 1)
    (F' := B0579.pd 1 (cutG R m Φ F 1)) (fun q η => slice_eta hG q η) hF' hi
  rw [cell_eq c] at key
  exact key

/-! ### Integrability of the pieces of one component -/

lemma int_S {c R m : ℝ} (hR : 0 < R) {Φ F : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (hF : ContDiff ℝ ∞ F) (k : Fin 2) :
    IntegrableOn (fun x => (ladCut R x ^ 2 * B0579.jb x ^ (-m)) *
      ((starRingEnd ℂ) (pdCx k (pdCx k Φ) x) * F x).re) (B0579.cell c) := by
  have hu : ContDiff ℝ ∞ (pdCx k Φ) := contDiff_pdCx' hΦ k
  refine integrableOn_cell_strict hR ((contDiff_Aw R m).continuous.mul
    (contDiff_re_conj_mul (contDiff_pdCx' hu k) hF).continuous) (fun x hx => ?_)
  simp [ladCut_zero' hR hx.le]

lemma int_Q {c R m : ℝ} (hR : 0 < R) {Φ F : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (hF : ContDiff ℝ ∞ F) (k : Fin 2) :
    IntegrableOn (fun x => B0579.pd k (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
      ((starRingEnd ℂ) (pdCx k Φ x) * F x).re) (B0579.cell c) := by
  refine integrableOn_cell_strict hR ((continuous_pd (contDiff_Aw R m) k).mul
    (contDiff_re_conj_mul (contDiff_pdCx' hΦ k) hF).continuous) (fun x hx => ?_)
  simp [pd_eq_zero_of_ev k (ev_zero_Aw hR hx)]

/-! ### One component -/

lemma perk_split {c R m : ℝ} (hR : 0 < R) {Φ F : ℝ × ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (hF : ContDiff ℝ ∞ F) (k : Fin 2)
    (hP : ∫ x in B0579.cell c, B0579.pd k (cutG R m Φ F k) x = 0) :
    ∫ x in B0579.cell c, ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
        (2 * ((starRingEnd ℂ) (pdCx k Φ x) * pdCx k F x).re)) =
      -(2 * ∫ x in B0579.cell c, B0579.pd k (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
          ((starRingEnd ℂ) (pdCx k Φ x) * F x).re) -
        2 * ∫ x in B0579.cell c, (ladCut R x ^ 2 * B0579.jb x ^ (-m)) *
          ((starRingEnd ℂ) (pdCx k (pdCx k Φ) x) * F x).re := by
  have iP : IntegrableOn (fun x => B0579.pd k (cutG R m Φ F k) x) (B0579.cell c) :=
    integrableOn_cell_strict hR (continuous_pd (contDiff_cutG hΦ hF k) k)
      (fun x hx => pd_eq_zero_of_ev k (cutG_ev_zero hR k hx))
  have iQ := int_Q (c := c) (m := m) hR hΦ hF k
  have iS := int_S (c := c) (m := m) hR hΦ hF k
  have hsplit : (fun x => ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
        (2 * ((starRingEnd ℂ) (pdCx k Φ x) * pdCx k F x).re))) =
      fun x => 2 * B0579.pd k (cutG R m Φ F k) x
        - 2 * (B0579.pd k (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
            ((starRingEnd ℂ) (pdCx k Φ x) * F x).re)
        - 2 * ((ladCut R x ^ 2 * B0579.jb x ^ (-m)) *
            ((starRingEnd ℂ) (pdCx k (pdCx k Φ) x) * F x).re) := by
    funext x
    rw [pd_cutG hΦ hF k x]
    ring
  have i1 : Integrable (fun x => 2 * B0579.pd k (cutG R m Φ F k) x
      - 2 * (B0579.pd k (fun y => ladCut R y ^ 2 * B0579.jb y ^ (-m)) x *
            ((starRingEnd ℂ) (pdCx k Φ x) * F x).re))
      (volume.restrict (B0579.cell c)) :=
    (Integrable.const_mul iP 2).sub (Integrable.const_mul iQ 2)
  have i2 : Integrable (fun x => 2 * ((ladCut R x ^ 2 * B0579.jb x ^ (-m)) *
      ((starRingEnd ℂ) (pdCx k (pdCx k Φ) x) * F x).re)) (volume.restrict (B0579.cell c)) :=
    Integrable.const_mul iS 2
  rw [hsplit, integral_sub i1 i2, integral_sub (Integrable.const_mul iP 2) (Integrable.const_mul iQ 2),
    integral_const_mul, integral_const_mul, integral_const_mul, hP]
  ring

end CutIBPAux

/-! ### The cut integration by parts -/

open CutIBPAux in
theorem cutIBP : UnforcedLeray.Short.IIIa.CutIBP := by
  intro c m R Φ F hc hR hΦ hF hΦper hFper
  have hΦ' : ContDiff ℝ ∞ Φ := hΦ
  have hF' : ContDiff ℝ ∞ F := hF
  unfold cutRate
  rw [Fin.sum_univ_two, Fin.sum_univ_two,
    perk_split hR hΦ' hF' 0 (ibp_q hc hR hΦ' hF' hΦper hFper),
    perk_split hR hΦ' hF' 1 (ibp_eta hR hΦ' hF')]
  have hLap : ∫ x in B0579.cell c, ladCut R x ^ 2 * (B0579.jb x ^ (-m) *
      ((starRingEnd ℂ) (ladLapCx Φ x) * F x).re) =
      (∫ x in B0579.cell c, (ladCut R x ^ 2 * B0579.jb x ^ (-m)) *
        ((starRingEnd ℂ) (pdCx 0 (pdCx 0 Φ) x) * F x).re) +
      ∫ x in B0579.cell c, (ladCut R x ^ 2 * B0579.jb x ^ (-m)) *
        ((starRingEnd ℂ) (pdCx 1 (pdCx 1 Φ) x) * F x).re := by
    rw [← integral_add (int_S (c := c) (m := m) hR hΦ' hF' 0) (int_S (c := c) (m := m) hR hΦ' hF' 1)]
    congr 1
    funext x
    simp only [ladLapCx, map_add, add_mul, Complex.add_re]
    ring
  rw [hLap]
  ring

end UnforcedLeray.Short.IIIa
