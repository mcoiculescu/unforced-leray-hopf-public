import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_3_1.AgeIBP

/-!
# Viscous `(q, η)` integration by parts for the scalar resolvent pairing
(helper of `PartIII-b:C/flatset/col/7/1/1/3/1`)

For each age slice `s > 0`, uses `B0610.hasWeakCellDeriv_of_smooth` on `B0579.cell c` to integrate
`-ν s^{-1/2} θ_S(s) f Δ_{q,η}(χ_R f)` by parts on the cylinder cell, yielding the positive gradient
term `viscMain` plus the `η`-cutoff derivative error `viscErr`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ComplexConjugate InnerProductSpace ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.B0220 (Profile)
open UnforcedLeray.Short.IIIa (flatLap)
open UnforcedLeray.Short.PartIIa (pdQ pdEta)

theorem pdQ_pdEta_eq_pd_slice {ψ : Profile → ℝ} (hψ : ContDiff ℝ ∞ ψ) (p : Profile) :
    pdQ (pdQ ψ) p + pdEta (pdEta ψ) p =
      B0579.pd 0 (B0579.pd 0 (fun y => ψ (p.1, y))) p.2 +
      B0579.pd 1 (B0579.pd 1 (fun y => ψ (p.1, y))) p.2 :=
  (flatLap_split' (Φ := fun s x _ => ψ (s, x)) (i := 0) hψ p).symm

/-- `χ_R(η)` as a function on `B0579.Plane = ℝ × ℝ`. -/
def chiPlane (R : ℝ) (x : B0579.Plane) : ℝ := chiR R x.2

theorem isCylTest_chiPlane {c R : ℝ} (hR : 0 < R) : B0579.IsCylTest c (chiPlane R) where
  smooth := (contDiff_chiR R).comp contDiff_snd
  periodic _ := rfl
  band := ⟨2 * R, fun _ hx => chiR_eq_zero hR hx.le⟩

theorem pd0_chiPlane (R : ℝ) (x : B0579.Plane) : B0579.pd 0 (chiPlane R) x = 0 := by
  have h1 := B0579.hasDerivAt_fst
    (((contDiff_chiR R).comp contDiff_snd).differentiable (by simp)) x.1 x.2
  have h2 : HasDerivAt (fun q : ℝ => chiPlane R (q, x.2)) 0 x.1 :=
    hasDerivAt_const x.1 (chiR R x.2)
  exact h1.unique h2

theorem pd1_chiPlane (R : ℝ) (x : B0579.Plane) : B0579.pd 1 (chiPlane R) x = deriv (chiR R) x.2 := by
  have h1 := B0579.hasDerivAt_snd
    (((contDiff_chiR R).comp contDiff_snd).differentiable (by simp)) x.1 x.2
  have h2 : HasDerivAt (fun η : ℝ => chiPlane R (x.1, η)) (deriv (chiR R) x.2) x.2 :=
    ((contDiff_chiR R).differentiable (by simp) x.2).hasDerivAt
  exact h1.unique h2

theorem pd_const_mul (a : ℝ) {g : B0579.Plane → ℝ} (hg : Differentiable ℝ g)
    (j : Fin 2) (x : B0579.Plane) :
    B0579.pd j (fun y => a * g y) x = a * B0579.pd j g x := by
  have h := B0579.pd_mul (differentiable_const a) hg j x
  have h0 : B0579.pd j (fun _ : B0579.Plane => a) x = 0 := by
    unfold B0579.pd
    simp
  rw [h0, zero_mul, zero_add] at h
  exact h

/-- Slice test `φ(y) = f(s, y) χ_R(y.2)` at fixed `s`. -/
def phiSlice (R : ℝ) (f : Profile → ℝ) (s : ℝ) (y : B0579.Plane) : ℝ :=
  f (s, y) * chiPlane R y

theorem isCylTest_phiSlice {c R : ℝ} (hR : 0 < R) {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : ∀ s q η : ℝ, f (s, (q + c, η)) = f (s, (q, η))) (s : ℝ) :
    B0579.IsCylTest c (phiSlice R f s) := by
  have hfs : ContDiff ℝ ∞ (fun y : B0579.Plane => f (s, y)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  exact B0610.isCylTest_smooth_mul hfs (fun y => hper s y.1 y.2) (isCylTest_chiPlane hR)

theorem slice_ibp_zero {c R : ℝ} (hR : 0 < R) {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : ∀ s q η : ℝ, f (s, (q + c, η)) = f (s, (q, η))) (s : ℝ) :
    -∫ x in B0579.cell c, f (s, x) * B0579.pd 0 (B0579.pd 0 (phiSlice R f s)) x =
      ∫ x in B0579.cell c, chiR R x.2 * (B0579.pd 0 (fun y => f (s, y)) x) ^ 2 := by
  have hfs : ContDiff ℝ ∞ (fun y : B0579.Plane => f (s, y)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hφ := isCylTest_phiSlice hR hf hper s
  have hw := B0610.hasWeakCellDeriv_of_smooth hfs (fun y => hper s y.1 y.2) 0
    (B0579.pd 0 (phiSlice R f s)) (hφ.pd 0)
  rw [hw, neg_neg]
  refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun x _ => ?_
  have hmul := B0579.pd_mul (hfs.differentiable (by simp))
    (isCylTest_chiPlane (c := c) hR).differentiable 0 x
  change B0579.pd 0 (fun y => f (s, y)) x * B0579.pd 0 (phiSlice R f s) x = _
  unfold phiSlice
  rw [hmul, pd0_chiPlane]
  unfold chiPlane
  ring

theorem slice_ibp_one {c R : ℝ} (hR : 0 < R) {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : ∀ s q η : ℝ, f (s, (q + c, η)) = f (s, (q, η))) (s : ℝ) :
    -∫ x in B0579.cell c, f (s, x) * B0579.pd 1 (B0579.pd 1 (phiSlice R f s)) x =
      ∫ x in B0579.cell c,
        (chiR R x.2 * (B0579.pd 1 (fun y => f (s, y)) x) ^ 2 +
         deriv (chiR R) x.2 * f (s, x) * B0579.pd 1 (fun y => f (s, y)) x) := by
  have hfs : ContDiff ℝ ∞ (fun y : B0579.Plane => f (s, y)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hφ := isCylTest_phiSlice hR hf hper s
  have hw := B0610.hasWeakCellDeriv_of_smooth hfs (fun y => hper s y.1 y.2) 1
    (B0579.pd 1 (phiSlice R f s)) (hφ.pd 1)
  rw [hw, neg_neg]
  refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun x _ => ?_
  have hmul := B0579.pd_mul (hfs.differentiable (by simp))
    (isCylTest_chiPlane (c := c) hR).differentiable 1 x
  change B0579.pd 1 (fun y => f (s, y)) x * B0579.pd 1 (phiSlice R f s) x = _
  unfold phiSlice
  rw [hmul, pd1_chiPlane]
  unfold chiPlane
  ring

/-- Main positive gradient density from the `(q, η)` integration by parts. -/
def viscMain (ν S R : ℝ) (f : Profile → ℝ) (p : Chart) : ℝ :=
  p.1 ^ (-(1 / 2 : ℝ)) * (ν * thetaS S p.1 * chiR R p.2.2 *
    (B0579.pd 0 (fun y => f (p.1, y)) p.2 ^ 2 +
     B0579.pd 1 (fun y => f (p.1, y)) p.2 ^ 2))

/-- Cutoff-derivative error density from the `η` integration by parts. -/
def viscErr (ν S R : ℝ) (f : Profile → ℝ) (p : Chart) : ℝ :=
  p.1 ^ (-(1 / 2 : ℝ)) * (ν * thetaS S p.1 * deriv (chiR R) p.2.2 *
    f p * B0579.pd 1 (fun y => f (p.1, y)) p.2)

theorem continuous_pd_slice {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f) (j : Fin 2) :
    Continuous (fun p : Chart => B0579.pd j (fun y => f (p.1, y)) p.2) := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  fin_cases j
  · dsimp only [Fin.zero_eta]
    have heq : (fun p : Chart => B0579.pd 0 (fun y => f (p.1, y)) p.2) = Axi.dQ f :=
      funext fun p => pd0_slice hfd p.1 p.2
    rw [heq]
    exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  · dsimp only [Fin.mk_one]
    have heq : (fun p : Chart => B0579.pd 1 (fun y => f (p.1, y)) p.2) = Axi.dEta f :=
      funext fun p => pd1_slice hfd p.1 p.2
    rw [heq]
    exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const

theorem pd_slice_zero_of_lt {s0 : ℝ} {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f)
    (hz : ∀ p : Profile, p.1 < s0 → f p = 0) (j : Fin 2) {p : Chart} (hp : p.1 < s0) :
    B0579.pd j (fun y => f (p.1, y)) p.2 = 0 := by
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  fin_cases j
  · dsimp only [Fin.zero_eta]
    rw [pd0_slice hfd p.1 p.2]
    unfold Axi.dQ
    rw [fderiv_zero_of_lt hz hp]
    simp
  · dsimp only [Fin.mk_one]
    rw [pd1_slice hfd p.1 p.2]
    unfold Axi.dEta
    rw [fderiv_zero_of_lt hz hp]
    simp

theorem deriv_chiR_eq_zero {R η : ℝ} (hR : 0 < R) (h : 2 * R < |η|) :
    deriv (chiR R) η = 0 := by
  have hU : IsOpen {t : ℝ | 2 * R < |t|} := isOpen_lt continuous_const continuous_abs
  have hev : chiR R =ᶠ[𝓝 η] fun _ => (0 : ℝ) :=
    Filter.eventually_of_mem (hU.mem_nhds h) fun t ht => chiR_eq_zero hR ht.le
  rw [hev.deriv_eq, deriv_const]

theorem integrableOn_viscMain {c s0 ν S R : ℝ} (hs0 : 0 < s0) (hR : 0 < R)
    {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f) (hz : ∀ p : Profile, p.1 < s0 → f p = 0) :
    IntegrableOn (viscMain ν S R f) (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  have hG : Continuous (fun p : Chart => ν * thetaS S p.1 * chiR R p.2.2 *
      (B0579.pd 0 (fun y => f (p.1, y)) p.2 ^ 2 +
       B0579.pd 1 (fun y => f (p.1, y)) p.2 ^ 2)) :=
    (((continuous_const.mul ((contDiff_thetaS S).continuous.comp continuous_fst)).mul
      ((contDiff_chiR R).continuous.comp (continuous_snd.comp continuous_snd))).mul
      (((continuous_pd_slice hf 0).pow 2).add ((continuous_pd_slice hf 1).pow 2)))
  refine integrableOn_of_band (s0 := s0) (s1 := max s0 (S + 1)) (L := 2 * R)
    (continuous_rpow_mul_of_zero_below hs0 _ hG
      (fun p hp => by
        rw [pd_slice_zero_of_lt hf hz 0 hp, pd_slice_zero_of_lt hf hz 1 hp]
        ring)) ?_
  intro p hp
  unfold viscMain
  rcases hp with h | h | h
  · rw [pd_slice_zero_of_lt hf hz 0 h, pd_slice_zero_of_lt hf hz 1 h]; ring
  · rw [thetaS_eq_zero (le_trans (le_max_right s0 (S + 1)) h.le)]; ring
  · rw [chiR_eq_zero hR h.le]; ring

theorem integrableOn_viscErr {c s0 ν S R : ℝ} (hs0 : 0 < s0) (hR : 0 < R)
    {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f) (hz : ∀ p : Profile, p.1 < s0 → f p = 0) :
    IntegrableOn (viscErr ν S R f) (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  have hG : Continuous (fun p : Chart => ν * thetaS S p.1 * deriv (chiR R) p.2.2 *
      f p * B0579.pd 1 (fun y => f (p.1, y)) p.2) :=
    ((((continuous_const.mul ((contDiff_thetaS S).continuous.comp continuous_fst)).mul
      (((contDiff_chiR R).continuous_deriv (by simp)).comp (continuous_snd.comp continuous_snd))).mul
      hf.continuous).mul (continuous_pd_slice hf 1))
  refine integrableOn_of_band (s0 := s0) (s1 := max s0 (S + 1)) (L := 2 * R)
    (continuous_rpow_mul_of_zero_below hs0 _ hG
      (fun p hp => by rw [hz p hp]; ring)) ?_
  intro p hp
  unfold viscErr
  rcases hp with h | h | h
  · rw [hz p h]; ring
  · rw [thetaS_eq_zero (le_trans (le_max_right s0 (S + 1)) h.le)]; ring
  · rw [deriv_chiR_eq_zero hR h]; ring

theorem integrableOn_viscIntegrand {c s0 ν S R : ℝ} (hs0 : 0 < s0) (hR : 0 < R)
    {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f) (hz : ∀ p : Profile, p.1 < s0 → f p = 0) :
    IntegrableOn (viscIntegrand ν S R f) (Ioi (0 : ℝ) ×ˢ B0579.cell c) := by
  have hfc := contDiff_fCut S R hf
  have hpdQ : Continuous (pdQ (pdQ (fCut S R f))) := by
    have h1 : ContDiff ℝ ∞ (pdQ (fCut S R f)) :=
      (hfc.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact (h1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpdE : Continuous (pdEta (pdEta (fCut S R f))) := by
    have h1 : ContDiff ℝ ∞ (pdEta (fCut S R f)) :=
      (hfc.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    exact (h1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hG : Continuous (fun p : Chart => -(ν * p.1 *
      (pdQ (pdQ (fCut S R f)) p + pdEta (pdEta (fCut S R f)) p) * f p)) :=
    (((continuous_const.mul continuous_fst).mul (hpdQ.add hpdE)).mul hf.continuous).neg
  have hcont := continuous_rpow_mul_of_zero_below hs0 (-(3 / 2 : ℝ)) hG
    (fun p hp => by rw [hz p hp]; ring)
  have heq : viscIntegrand ν S R f = fun p : Chart => p.1 ^ (-(3 / 2 : ℝ)) *
      (-(ν * p.1 * (pdQ (pdQ (fCut S R f)) p + pdEta (pdEta (fCut S R f)) p) * f p)) := by
    funext p; unfold viscIntegrand; ring
  rw [heq]
  refine integrableOn_of_band (s0 := s0) (s1 := max s0 (S + 1)) (L := 2 * R) hcont ?_
  intro p hp
  have houtQ : ∀ q : Profile, (q.1 < s0 ∨ max s0 (S + 1) < q.1 ∨ 2 * R < |q.2.2|) →
      pdQ (fCut S R f) q = 0 := by
    intro q hq
    unfold pdQ
    rw [fderiv_zero_outside_band (fun r hr => fCut_zero_outside_band hR hz hr) hq]
    simp
  have houtE : ∀ q : Profile, (q.1 < s0 ∨ max s0 (S + 1) < q.1 ∨ 2 * R < |q.2.2|) →
      pdEta (fCut S R f) q = 0 := by
    intro q hq
    unfold pdEta
    rw [fderiv_zero_outside_band (fun r hr => fCut_zero_outside_band hR hz hr) hq]
    simp
  have hQ0 : pdQ (pdQ (fCut S R f)) p = 0 := by
    change fderiv ℝ (pdQ (fCut S R f)) p (0, 1, 0) = 0
    rw [fderiv_zero_outside_band houtQ hp]
    simp
  have hE0 : pdEta (pdEta (fCut S R f)) p = 0 := by
    change fderiv ℝ (pdEta (fCut S R f)) p (0, 0, 1) = 0
    rw [fderiv_zero_outside_band houtE hp]
    simp
  rw [hQ0, hE0]
  ring

theorem viscIntegrand_slice_eq {c ν S R : ℝ} (hR : 0 < R) {f : Profile → ℝ}
    (hf : ContDiff ℝ ∞ f) (hper : ∀ s q η : ℝ, f (s, (q + c, η)) = f (s, (q, η)))
    {s : ℝ} (hs : 0 < s) :
    ∫ x in B0579.cell c, viscIntegrand ν S R f (s, x) =
      ∫ x in B0579.cell c, (viscMain ν S R f (s, x) + viscErr ν S R f (s, x)) := by
  have hr : s ^ (-(3 / 2 : ℝ)) * (ν * s) = ν * s ^ (-(1 / 2 : ℝ)) := by
    have h1 : s ^ (-(3 / 2 : ℝ)) * s = s ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add_one hs.ne']
      congr 1; ring
    calc s ^ (-(3 / 2 : ℝ)) * (ν * s) = ν * (s ^ (-(3 / 2 : ℝ)) * s) := by ring
      _ = ν * s ^ (-(1 / 2 : ℝ)) := by rw [h1]
  have hφ := isCylTest_phiSlice (c := c) hR hf hper s
  have hfs : ContDiff ℝ ∞ (fun y : B0579.Plane => f (s, y)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hfCut_slice : (fun y : B0579.Plane => fCut S R f (s, y)) =
      fun y => thetaS S s * phiSlice R f s y := by
    funext y; unfold fCut phiSlice chiPlane; ring
  have hpd2 : ∀ (j : Fin 2) (x : B0579.Plane),
      B0579.pd j (B0579.pd j (fun y => fCut S R f (s, y))) x =
        thetaS S s * B0579.pd j (B0579.pd j (phiSlice R f s)) x := by
    intro j x
    rw [hfCut_slice]
    have h1 : B0579.pd j (fun y => thetaS S s * phiSlice R f s y) =
        fun y => thetaS S s * B0579.pd j (phiSlice R f s) y :=
      funext fun y => pd_const_mul (thetaS S s) hφ.differentiable j y
    rw [h1, pd_const_mul (thetaS S s) (hφ.pd j).differentiable j x]
  have hpt : ∀ x : B0579.Plane, viscIntegrand ν S R f (s, x) =
      (s ^ (-(1 / 2 : ℝ)) * ν * thetaS S s) *
        (-(f (s, x) * B0579.pd 0 (B0579.pd 0 (phiSlice R f s)) x) +
         -(f (s, x) * B0579.pd 1 (B0579.pd 1 (phiSlice R f s)) x)) := by
    intro x
    unfold viscIntegrand
    rw [pdQ_pdEta_eq_pd_slice (contDiff_fCut S R hf) (s, x)]
    dsimp only
    rw [hpd2 0 x, hpd2 1 x, hr]
    ring
  have hI0 : IntegrableOn (fun x => -(f (s, x) * B0579.pd 0 (B0579.pd 0 (phiSlice R f s)) x))
      (B0579.cell c) := by
    have htest : B0579.IsCylTest c (fun x => f (s, x) * B0579.pd 0 (B0579.pd 0 (phiSlice R f s)) x) :=
      B0610.isCylTest_smooth_mul hfs (fun y => hper s y.1 y.2) ((hφ.pd 0).pd 0)
    exact htest.integrableOn.neg
  have hI1 : IntegrableOn (fun x => -(f (s, x) * B0579.pd 1 (B0579.pd 1 (phiSlice R f s)) x))
      (B0579.cell c) := by
    have htest : B0579.IsCylTest c (fun x => f (s, x) * B0579.pd 1 (B0579.pd 1 (phiSlice R f s)) x) :=
      B0610.isCylTest_smooth_mul hfs (fun y => hper s y.1 y.2) ((hφ.pd 1).pd 1)
    exact htest.integrableOn.neg
  have hJ0 : IntegrableOn (fun x : B0579.Plane =>
      chiR R x.2 * (B0579.pd 0 (fun y => f (s, y)) x) ^ 2) (B0579.cell c) := by
    have hcont0 : Continuous (fun x : B0579.Plane =>
        chiR R x.2 * (B0579.pd 0 (fun y => f (s, y)) x) ^ 2) :=
      ((contDiff_chiR R).continuous.comp continuous_snd).mul
        ((B0579.contDiff_pd hfs 0).continuous.pow 2)
    refine B0579.integrableOn_cell_of_continuous hcont0 (B0579.isCompact_box c (2 * R))
      (fun x hx hxK => ?_)
    have hgt : 2 * R < |x.2| := by
      by_contra hle; exact hxK (B0579.mem_box_of_mem_cell hx (not_lt.1 hle))
    rw [chiR_eq_zero hR hgt.le, zero_mul]
  have hJ1 : IntegrableOn (fun x : B0579.Plane =>
      chiR R x.2 * (B0579.pd 1 (fun y => f (s, y)) x) ^ 2 +
      deriv (chiR R) x.2 * f (s, x) * B0579.pd 1 (fun y => f (s, y)) x) (B0579.cell c) := by
    have hcont1 : Continuous (fun x : B0579.Plane =>
        chiR R x.2 * (B0579.pd 1 (fun y => f (s, y)) x) ^ 2 +
        deriv (chiR R) x.2 * f (s, x) * B0579.pd 1 (fun y => f (s, y)) x) :=
      (((contDiff_chiR R).continuous.comp continuous_snd).mul
        ((B0579.contDiff_pd hfs 1).continuous.pow 2)).add
        (((((contDiff_chiR R).continuous_deriv (by simp)).comp continuous_snd).mul
          hfs.continuous).mul (B0579.contDiff_pd hfs 1).continuous)
    refine B0579.integrableOn_cell_of_continuous hcont1 (B0579.isCompact_box c (2 * R))
      (fun x hx hxK => ?_)
    have hgt : 2 * R < |x.2| := by
      by_contra hle; exact hxK (B0579.mem_box_of_mem_cell hx (not_lt.1 hle))
    rw [chiR_eq_zero hR hgt.le, deriv_chiR_eq_zero hR hgt]
    ring
  rw [setIntegral_congr_fun (B0579.measurableSet_cell c) (fun x _ => hpt x),
    integral_const_mul, integral_add hI0 hI1, integral_neg, integral_neg,
    slice_ibp_zero hR hf hper s, slice_ibp_one hR hf hper s,
    ← integral_add hJ0 hJ1, ← integral_const_mul]
  refine setIntegral_congr_fun (B0579.measurableSet_cell c) fun x _ => ?_
  unfold viscMain viscErr
  dsimp only [Pi.add_apply]
  ring

/-- **Main viscous IBP identity**: the cylinder integral of `viscIntegrand ν S R f` splits into
`viscMain` and `viscErr`. -/
theorem integral_viscIntegrand_eq {c s0 ν S R : ℝ} (hs0 : 0 < s0) (hR : 0 < R)
    {f : Profile → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : ∀ s q η : ℝ, f (s, (q + c, η)) = f (s, (q, η)))
    (hz : ∀ p : Profile, p.1 < s0 → f p = 0) :
    ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, viscIntegrand ν S R f p =
      (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, viscMain ν S R f p) +
      (∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, viscErr ν S R f p) := by
  have hI := integrableOn_viscIntegrand (c := c) (ν := ν) (S := S) hs0 hR hf hz
  have hM := integrableOn_viscMain (c := c) (ν := ν) (S := S) hs0 hR hf hz
  have hE := integrableOn_viscErr (c := c) (ν := ν) (S := S) hs0 hR hf hz
  have hME : IntegrableOn (fun p => viscMain ν S R f p + viscErr ν S R f p)
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) := hM.add hE
  rw [← integral_add hM hE]
  have hprod : (volume : Measure Chart).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c) =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (B0579.cell c)) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [IntegrableOn, hprod] at hI hME
  rw [hprod, integral_prod _ hI, integral_prod _ hME]
  refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
  exact viscIntegrand_slice_eq hR hf hper hs

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
