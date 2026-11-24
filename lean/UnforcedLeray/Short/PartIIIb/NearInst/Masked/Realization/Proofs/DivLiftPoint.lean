import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.ChartConj
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartDivPointwise
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.ChartStressIBP.BandSliceSmooth

/-!
# `DivLiftPoint` (source 1655-1665, 2682-2683)

Route.  Off the axis, `strPhys ε⁻¹ c m` is jointly `C¹` in `(τ, y)` (`dlp_strPhys_contDiffAt`,
from the sandwich formula `strPhys_eq_sandwich`).  The outer field `x ↦ strPhys (τ, ε⁻¹ x)` has
spatial derivative `ε⁻¹ · ∂_y` (`dlp_fderiv_scale`).  The pointwise chart identity
`chartDivPointwise` gives the real chart field `G₀ = G0 ε m` (`s · div_ε m`) with velocity lift
`velPhys`.  The chart point of `(x, τ)` is the cell point of `cellChart` up to a `c`-period
(`per_int`), and `√age = 1/r = liftA x`, `frameL (ε⁻¹ x) = frame x`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-! ## Joint smoothness of the Cartesian lift off the axis -/

theorem dlp_hRad_snd {τ : ℝ} {y : Space} (hy : 0 < hRad y) :
    ContDiffAt ℝ 1 (fun p : ℝ × Space => hRad p.2) (τ, y) :=
  ContDiffAt.comp (f := fun p : ℝ × Space => p.2) (g := fun z : Space => hRad z) (τ, y)
    (NearInst.hRad_contDiffAt_pos hy) contDiffAt_snd

theorem dlp_ptOf_contDiffAt {R : ℝ} (hR : 0 < R) {τ : ℝ} {y : Space} (hy : 0 < hRad y) :
    ContDiffAt ℝ 1 (fun p : ℝ × Space => NearInst.ptOf R p.1 p.2) (τ, y) := by
  have hy0 : ∀ k : Fin 3, ContDiff ℝ 1 (fun z : Space => z k) := fun k =>
    (contDiff_piLp (p := 2)).mp contDiff_id k
  have hRC : ContDiffAt ℝ 1 (fun p : ℝ × Space => hRad p.2) (τ, y) := dlp_hRad_snd hy
  have hS : ContDiffAt ℝ 1 (fun p : ℝ × Space => p.2 2) (τ, y) :=
    (hy0 2).contDiffAt.comp (τ, y) contDiffAt_snd
  have hs : ContDiffAt ℝ 1 (fun p : ℝ × Space => R ^ 2 / hRad p.2 ^ 2) (τ, y) :=
    contDiffAt_const.div (hRC.pow 2) (pow_ne_zero 2 hy.ne')
  have hQ : ContDiffAt ℝ 1
      (fun p : ℝ × Space => R * Real.log (hRad p.2 / R) + R * p.1 / 2) (τ, y) :=
    (contDiffAt_const.mul ((hRC.div_const R).log (div_ne_zero hy.ne' hR.ne'))).add
      ((contDiffAt_const.mul contDiffAt_fst).div_const 2)
  have hη : ContDiffAt ℝ 1 (fun p : ℝ × Space => R * p.2 2 / hRad p.2) (τ, y) :=
    (contDiffAt_const.mul hS).div hRC hy.ne'
  exact hs.prodMk (hQ.prodMk hη)

theorem dlp_strPhys_contDiffAt {c R : ℝ} (hR : 0 < R) (M : Chart → Ten3)
    (hM : UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x)))
    {τ : ℝ} {y : Space} (hy : 0 < hRad y) (i j : Fin 3) :
    ContDiffAt ℝ 1 (fun p : ℝ × Space => strPhys R c M p i j) (τ, y) := by
  have hpt := dlp_ptOf_contDiffAt hR (τ := τ) hy
  have hN : ∀ a b : Fin 3, ContDiffAt ℝ 1
      (fun p : ℝ × Space => nsSym (M (NearInst.ptOf R p.1 p.2)) a b) (τ, y) := fun a b =>
    (NearInst.nsSym_entry_contDiff M hM a b).contDiffAt.comp (τ, y) hpt
  have hC : ∀ a b : Fin 3, ContDiffAt ℝ 1 (fun p : ℝ × Space => cylFrame p.2 a b) (τ, y) :=
    fun a b => (NearInst.cylFrame_entry_contDiffAt hy a b).comp (τ, y) contDiffAt_snd
  have hs : ContDiffAt ℝ 1 (fun p : ℝ × Space => R ^ 2 / hRad p.2 ^ 2) (τ, y) :=
    contDiffAt_const.div ((dlp_hRad_snd hy).pow 2) (pow_ne_zero 2 hy.ne')
  have hfun : (fun p : ℝ × Space => strPhys R c M p i j) = fun p : ℝ × Space =>
      (cylFrame p.2 * ((R ^ 2 / hRad p.2 ^ 2) • nsSym (M (NearInst.ptOf R p.1 p.2)))
        * (cylFrame p.2).transpose) i j := by
    funext p
    show strPhys R c M (p.1, p.2) i j = _
    rw [NearInst.strPhys_eq_sandwich R c p.1 M hM p.2]
  rw [hfun]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  refine ContDiffAt.sum fun k _ => ?_
  refine ContDiffAt.mul ?_ (hC j k)
  refine ContDiffAt.sum fun l _ => ?_
  exact (hC i l).mul (hs.mul (hN l k))

/-! ## Chain rule for the outer scaling `x ↦ ε⁻¹ x` -/

theorem dlp_fderiv_scale (R : ℝ) (Ψ : ℝ × Space → ℝ) (τ : ℝ) (x : Space)
    (hΨ : DifferentiableAt ℝ Ψ (τ, R • x)) (v : Space) :
    fderiv ℝ (fun x' : Space => Ψ (τ, R • x')) x v = R * fderiv ℝ Ψ (τ, R • x) (0, v) := by
  have g : HasFDerivAt (fun x' : Space => ((τ, R • x') : ℝ × Space))
      ((0 : Space →L[ℝ] ℝ).prod (R • ContinuousLinearMap.id ℝ Space)) x :=
    (hasFDerivAt_const τ x).prodMk ((hasFDerivAt_id x).const_smul R)
  have h := hΨ.hasFDerivAt.comp x g
  have e : (fun x' : Space => Ψ (τ, R • x')) =
      Ψ ∘ (fun x' : Space => ((τ, R • x') : ℝ × Space)) := rfl
  rw [e, h.fderiv]
  have hL : ((0 : Space →L[ℝ] ℝ).prod (R • ContinuousLinearMap.id ℝ Space)) v =
      R • ((0 : ℝ), v) :=
    Prod.ext (by simp) (by simp)
  rw [ContinuousLinearMap.comp_apply, hL, map_smul, smul_eq_mul]

/-! ## Geometry of the outer scaling -/

theorem dlp_ϱ_smul {R : ℝ} (hR : 0 < R) (z : Space) :
    UnforcedLeray.Axi.ϱ (R • z) = R * UnforcedLeray.B0220.radius z := by
  unfold UnforcedLeray.Axi.ϱ UnforcedLeray.B0220.radius
  rw [show (R • z) 0 ^ 2 + (R • z) 1 ^ 2 = R ^ 2 * (z 0 ^ 2 + z 1 ^ 2) by
    simp only [PiLp.smul_apply, smul_eq_mul]; ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hR.le]

theorem dlp_frameL_eq {R : ℝ} (hR : 0 < R) {x : Space} (hx : UnforcedLeray.B0220.radius x ≠ 0)
    (D : Merid) :
    UnforcedLeray.Axi.frameL (R • x) D = UnforcedLeray.B0220.frame x D := by
  have he : UnforcedLeray.Axi.eR (R • x) = UnforcedLeray.B0220.unitR x := by
    ext i
    fin_cases i
    · show UnforcedLeray.Axi.eR (R • x) 0 = UnforcedLeray.B0220.unitR x 0
      rw [UnforcedLeray.Axi.eR_apply_zero, dlp_ϱ_smul hR]
      simp [UnforcedLeray.B0220.unitR, EuclideanSpace.single_apply] <;> field_simp
    · show UnforcedLeray.Axi.eR (R • x) 1 = UnforcedLeray.B0220.unitR x 1
      rw [UnforcedLeray.Axi.eR_apply_one, dlp_ϱ_smul hR]
      simp [UnforcedLeray.B0220.unitR, EuclideanSpace.single_apply] <;> field_simp
    · show UnforcedLeray.Axi.eR (R • x) 2 = UnforcedLeray.B0220.unitR x 2
      rw [UnforcedLeray.Axi.eR_apply_two]
      simp [UnforcedLeray.B0220.unitR, EuclideanSpace.single_apply]
  rw [UnforcedLeray.Axi.frameL_apply, UnforcedLeray.B0220.frame_apply, he]
  rfl

/-! ## Assembly -/

theorem merC_inj_dlp {a b : Merid} (h : NearInst.merC a = NearInst.merC b) : a = b := by
  have := congrArg merReL h
  simpa [merReL_merC] using this

theorem divLiftPoint : DivLiftPoint := by
  intro ε c hε hc m hm x hx τ
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hr : 0 < UnforcedLeray.B0220.radius x :=
    lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hx)
  have hϱ : UnforcedLeray.Axi.ϱ (ε⁻¹ • x) = ε⁻¹ * UnforcedLeray.B0220.radius x :=
    dlp_ϱ_smul hR x
  have hy : 0 < hRad (ε⁻¹ • x) := by
    rw [hRad_eq, hϱ]; positivity
  have hyax : (ε⁻¹ • x) ∉ UnforcedLeray.Axi.axis := NearInst.notAxis_of_hRad hy
  -- chart identities
  have hageS : UnforcedLeray.Axi.age ε⁻¹ (ε⁻¹ • x) = UnforcedLeray.B0220.ageS x := by
    unfold UnforcedLeray.Axi.age UnforcedLeray.B0220.ageS
    rw [hϱ]
    field_simp
  have hetaS : UnforcedLeray.Axi.trans ε⁻¹ (ε⁻¹ • x) = UnforcedLeray.B0220.etaCoord ε x := by
    unfold UnforcedLeray.Axi.trans UnforcedLeray.B0220.etaCoord
    rw [hϱ]
    simp only [PiLp.smul_apply, smul_eq_mul]
    field_simp
  have hphase : UnforcedLeray.Axi.phase ε⁻¹ τ (ε⁻¹ • x) = UnforcedLeray.B0220.cellQ ε x τ := by
    unfold UnforcedLeray.Axi.phase UnforcedLeray.B0220.cellQ
    rw [hageS]
    unfold UnforcedLeray.B0220.ageS
    rw [Real.log_inv, Real.log_pow]
    push_cast
    ring
  have hsq : √(UnforcedLeray.Axi.age ε⁻¹ (ε⁻¹ • x)) = UnforcedLeray.B0220.liftA x := by
    rw [UnforcedLeray.Axi.sqrt_age hR hyax, hϱ]
    unfold UnforcedLeray.B0220.liftA
    field_simp
  -- the G0 field
  have hDER : ∀ p : Chart, NearInst.merC (G0 ε m p) =
      (p.1 : ℂ) • UnforcedLeray.Short.PartIIa.divEps ε (fun q => tv4 (m q)) p :=
    fun p => divEpsRealLeaf c ε m hm p
  have hG0smul : ∀ q : Chart, G0 ε m q =
      q.1 • merReL (UnforcedLeray.Short.PartIIa.divEps ε (fun p => tv4 (m p)) q) := by
    intro q
    rw [← merReL_merC (G0 ε m q), hDER q, merReL_ofReal_smul]
  have hGper : ∀ s Q η : ℝ, G0 ε m (s, (Q + c, η)) = G0 ε m (s, (Q, η)) :=
    fun s Q η => g0Periodic c ε m hm s Q η
  have hkey : ∀ s Q η : ℝ,
      G0 ε m (s, (Q, η)) = G0 ε m (s, (UnforcedLeray.B0220.reduceIoc c Q, η)) := by
    intro s Q η
    have h := per_int c (G0 ε m) hGper (⌈Q / c⌉ - 1) s (UnforcedLeray.B0220.reduceIoc c Q) η
    have e : UnforcedLeray.B0220.reduceIoc c Q + (((⌈Q / c⌉ - 1 : ℤ)) : ℝ) * c = Q := by
      unfold UnforcedLeray.B0220.reduceIoc
      push_cast
      ring
    rw [e] at h
    exact h
  have hchart : G0 ε m (UnforcedLeray.Axi.chart ε⁻¹ τ (ε⁻¹ • x)) =
      G0 ε m (UnforcedLeray.B0220.cellChart ε c (x, τ)) := by
    show G0 ε m (UnforcedLeray.Axi.age ε⁻¹ (ε⁻¹ • x),
      (UnforcedLeray.Axi.phase ε⁻¹ τ (ε⁻¹ • x), UnforcedLeray.Axi.trans ε⁻¹ (ε⁻¹ • x))) =
      G0 ε m (UnforcedLeray.B0220.ageS x,
        (UnforcedLeray.B0220.reduceIoc c (UnforcedLeray.B0220.cellQ ε x τ),
          UnforcedLeray.B0220.etaCoord ε x))
    rw [hageS, hphase, hetaS]
    exact hkey _ _ _
  -- the velocity field equals the real chart field G0
  obtain ⟨G₀, hG₀, hdiv⟩ := chartDivPointwise c ε hc hε m hm
  have hGG : G₀ = G0 ε m := by
    funext p
    apply merC_inj_dlp
    rw [hG₀ p, hDER p]
  have hper : ∀ s Q η : ℝ, G₀ (s, (Q + c, η)) = G₀ (s, (Q, η)) := by
    intro s Q η
    rw [hGG]
    exact hGper s Q η
  -- differentiability of the lift off the axis
  have hΨd : ∀ i j : Fin 3, DifferentiableAt ℝ
      (fun p : ℝ × Space => strPhys ε⁻¹ c m p i j) (τ, ε⁻¹ • x) := fun i j =>
    (dlp_strPhys_contDiffAt (c := c) hR m hm hy i j).differentiableAt (by norm_num)
  -- the outer divergence component is `ε⁻¹` times the joint spatial derivatives
  have hcomp : ∀ i : Fin 3, cartDiv (outerField ε⁻¹ (cartLift ε⁻¹ c m)) (x, τ) i =
      ε⁻¹ * ∑ j : Fin 3, UnforcedLeray.PhaseSpace.dy j
        (fun p : ℝ × Space => strPhys ε⁻¹ c m p i j) (τ, ε⁻¹ • x) := by
    intro i
    unfold cartDiv
    simp only [PiLp.toLp_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact dlp_fderiv_scale ε⁻¹ (fun p : ℝ × Space => strPhys ε⁻¹ c m p i j) τ x
      (hΨd i j) (UnforcedLeray.coordinateVector j)
  -- the velocity lift at the chart point, with the periodic extension of G₀ = G0
  have hNv : ∀ i : Fin 3, velPhys ε⁻¹ c G₀ (τ, ε⁻¹ • x) i =
      (((√(UnforcedLeray.Axi.age ε⁻¹ (ε⁻¹ • x))) *
        (UnforcedLeray.Axi.frameL (ε⁻¹ • x)
          (G0 ε m (UnforcedLeray.Axi.chart ε⁻¹ τ (ε⁻¹ • x)))) i : ℝ) : ℂ) := by
    intro i
    have e1 : UnforcedLeray.Axi.perExt c G₀
        (UnforcedLeray.Axi.chart ε⁻¹ τ (ε⁻¹ • x)) =
        G0 ε m (UnforcedLeray.Axi.chart ε⁻¹ τ (ε⁻¹ • x)) := by
      rw [NearInst.perExt_eq_of_per G₀ hper, hGG]
    rw [show velPhys ε⁻¹ c G₀ (τ, ε⁻¹ • x) =
        UnforcedLeray.B0412.realC
          (UnforcedLeray.Axi.Nv ε⁻¹ (UnforcedLeray.Axi.perExt c G₀) τ (ε⁻¹ • x)) from rfl,
      UnforcedLeray.B0412.realC_apply]
    unfold UnforcedLeray.Axi.Nv
    rw [e1]
    simp only [PiLp.smul_apply, smul_eq_mul]
  -- real form of the pointwise identity
  have hrel : ∀ i : Fin 3,
      ∑ j : Fin 3, UnforcedLeray.PhaseSpace.dy j
        (fun p : ℝ × Space => strPhys ε⁻¹ c m p i j) (τ, ε⁻¹ • x) =
      (√(UnforcedLeray.Axi.age ε⁻¹ (ε⁻¹ • x))) *
        (UnforcedLeray.Axi.frameL (ε⁻¹ • x)
          (G0 ε m (UnforcedLeray.Axi.chart ε⁻¹ τ (ε⁻¹ • x)))) i := by
    intro i
    have h := hdiv τ (ε⁻¹ • x) hy i
    have hc2 : ∀ j : Fin 3,
        UnforcedLeray.PhaseSpace.dy j (fun p : ℝ × Space => ((strPhys ε⁻¹ c m p i j : ℝ) : ℂ))
          (τ, ε⁻¹ • x) =
        (((UnforcedLeray.PhaseSpace.dy j (fun p : ℝ × Space => strPhys ε⁻¹ c m p i j)
          (τ, ε⁻¹ • x)) : ℝ) : ℂ) := fun j =>
      cylDiv_cplx (fun p : ℝ × Space => strPhys ε⁻¹ c m p i j) (τ, ε⁻¹ • x) (hΨd i j)
        (0, UnforcedLeray.coordinateVector j)
    rw [Finset.sum_congr rfl (fun j _ => hc2 j), hNv i, ← Complex.ofReal_sum] at h
    exact Complex.ofReal_injective h
  -- the chart point is the cell point up to a `c`-period
  have hcc : (UnforcedLeray.B0220.cellChart ε c (x, τ)).1 = UnforcedLeray.B0220.liftA x ^ 2 :=
    (UnforcedLeray.B0220.liftA_sq x).symm
  ext i
  rw [hcomp i, hrel i, hchart, hG0smul (UnforcedLeray.B0220.cellChart ε c (x, τ)), map_smul,
    dlp_frameL_eq hR hx, hsq, hcc]
  simp only [PiLp.smul_apply, smul_eq_mul]
  ring

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
