import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N04.Defs
import UnforcedLeray.Short.PartIIa.Tasks.N01StressMaps
import UnforcedLeray.Short.PartIIa.Tasks.F14SmoothStressMap
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.ChartConjSmooth

/-!
# Proof of `SymGradAdjointBound` for `PartII-a:N04`

Source of record: `the November 2 reference manuscript`,
lines 1848–1860 (adjoint symmetric-gradient / divergence pairing bound on `RepsVec* R`).

By `ContinuousLinearMap.adjoint_inner_right`,
`⟨G, RepsVec* R⟩_H = ⟨RepsVec G, R⟩_H`. For a smooth tensor test `Mtest` with `G =ᵐ s • divEps ε Mtest`,
the chart-to-phase lift carries `RepsVec G` to `(2π)^{-1/2} √(Pε) R_μ (div 𝒩_T Mtest)` without Leray
projection (`B0223.J_RepsVec`, `N01.phaseLift_physRes`, `N01.phaseDivScale`). Since `v = R_μ (div 𝒩_T Mtest)`
solves `(μ + L) v = div 𝒩_T Mtest` in `D₂` (`N01.bodyResolvent_bodyOp`), the `D₂` energy identity
`smoothStressEnergyD2` and divergence pairing `tensorDivPairingLe` (`PartII-a:F14/1`) bound `‖v‖_{Y₂}`
by `‖𝒩_T Mtest‖ / (2 √((Re μ + 1/4) ν))`, whence `‖RepsVec G‖_H ≤ 2 (1 + M + γs⁻¹) ν^{-1/2} ‖F‖_{H_T}`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.PartIIa.N04SymGradAux

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC SpaceC)
open UnforcedLeray.Short.PartIIIb.Concrete (Chart Ten3)
open UnforcedLeray.Short.PartIIIb.NearInst (tv4 cartLift)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked (merReL smul_divEps_im)
open UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

/-- Chart-to-Cartesian conjugation of `RepsVec` on a real smooth tensor test (without `PepsC`). -/
private theorem liftVec_RepsVec_real {ν ε c P : ℝ} [Fact (0 < P)]
    (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) {μ : ℂ} (hγ : 0 < μ.re + 1 / 4)
    (m : Chart → Ten3) (hm : IsTensorTest c (fun p => tv4 (m p)))
    (G : HSpace c MeridC)
    (hG : (G : Profile → MeridC) =ᵐ[measureH c]
      (fun p => (p.1 : ℂ) • divEps ε (fun q => tv4 (m q)) p)) :
    ∃ (_hTest : IsCartTest P (cartLift ε⁻¹ c m))
      (hM : MemLp (cartDiv (outerField ε⁻¹ (cartLift ε⁻¹ c m))) 2
        (UnforcedLeray.B0220.physMeasure ε c)),
      UnforcedLeray.B0223.liftVec hε hc hP (UnforcedLeray.B0223.RepsVec hν hε hc hP μ G) =
        (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) •
          UnforcedLeray.B0223.physRes (E := SpaceC) (P := P) hν ε μ
            (toX hP (hM.toLp (cartDiv (outerField ε⁻¹ (cartLift ε⁻¹ c m))))) := by
  have hT := cartLiftIsTest ε c P hε hc hP m hm
  have hM := cartTestDivMemLp ε c P hε hc hP _ hT
  refine ⟨hT, hM, ?_⟩
  have hreal : ∀ᵐ p ∂UnforcedLeray.B0220.measureH c,
      ∀ i, ((G : Profile → MeridC) p i).im = 0 := by
    filter_upwards [hG] with p hp i
    rw [hp]
    exact smul_divEps_im ε _ (fun p i => tv4_im (m p) i) p i
  set g := reHC c G
  have hGg : G = cplxH c g := (cplxH_reHC hreal).symm
  have hgb : (g : Profile → UnforcedLeray.B0220.Merid)
      =ᵐ[UnforcedLeray.B0220.measureH c] fun p =>
        merReL ((p.1 : ℂ) • divEps ε (fun p => tv4 (m p)) p) := by
    filter_upwards [reHC_ae c G, hG] with p h1 h2
    rw [h1, h2]
  set k : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ with hk
  have hJae : (UnforcedLeray.B0220.J hε hc g : Space × ℝ → Space)
      =ᵐ[UnforcedLeray.B0220.physMeasure ε c]
        fun y => k • cartDiv (outerField ε⁻¹ (cartLift ε⁻¹ c m)) y := by
    have h1 : (UnforcedLeray.B0220.J hε hc g : Space × ℝ → Space)
        =ᵐ[UnforcedLeray.B0220.physMeasure ε c]
          (UnforcedLeray.B0220.jComp hε hc).compFun g :=
      (UnforcedLeray.B0220.jComp hε hc).coeFn_toLI g
    have h2 := (UnforcedLeray.B0220.jComp hε hc).compFun_congr hgb
    filter_upwards [h1, h2, UnforcedLeray.B0220.ae_physMeasure ε c] with y hy1 hy2 hy3
    rw [hy1, hy2]
    obtain ⟨x, τ⟩ := y
    have hd := divLiftPoint ε c hε hc m hm x hy3.1 τ
    simp only [UnforcedLeray.B0220.WeightedComp.compFun, UnforcedLeray.B0220.jComp,
      LinearMap.smul_apply]
    rw [hd, merReL_ofReal_smul, map_smul, smul_smul, smul_smul]
    congr 1
    have hs : (UnforcedLeray.B0220.cellChart ε c (x, τ)).1 = UnforcedLeray.B0220.liftA x ^ 2 :=
      (UnforcedLeray.B0220.liftA_sq x).symm
    rw [hs, hk]
    unfold UnforcedLeray.B0220.jConst
    rw [mul_inv]
    ring
  have hJ : UnforcedLeray.B0220.J hε hc g =
      k • hM.toLp (cartDiv (outerField ε⁻¹ (cartLift ε⁻¹ c m))) := by
    apply Lp.ext
    filter_upwards [hJae, Lp.coeFn_smul k (hM.toLp (cartDiv (outerField ε⁻¹ (cartLift ε⁻¹ c m)))),
      hM.coeFn_toLp] with y h1 h2 h3
    rw [h1, h2, Pi.smul_apply, h3]
  rw [UnforcedLeray.B0223.J_RepsVec hν hε hc hP hγ G, hGg,
    liftVecCplx ε c P hε hc hP g, hJ, map_smul,
    ContinuousLinearMap.map_smul_of_tower, Complex.coe_smul]
  rfl

/-- Unprojected `D₂` energy bound for `(μ + L) w = div G_rows`. -/
private theorem bodyOp_div_norm_le {P : ℝ} [Fact (0 < P)] (hP1 : P ≤ 1) {ν : ℝ} (hν : 0 < ν)
    {μ : ℂ} (hγ : 0 < μ.re + 1 / 4) (w : D P ν 2)
    (G : Fin 3 → ℝ × Space → CVec3) (hG : ∀ i, IsPhaseTest P (G i)) (hs : IsSymRows G)
    (hsol : bodyOp P ν 2 μ w = testElem P 2 (tensorDiv G)) :
    ‖(w : Yq P 2)‖ ≤ ‖smoothTensor P G‖ / (2 * Real.sqrt ((μ.re + 1 / 4) * ν)) := by
  obtain ⟨g', hg', hid⟩ := smoothStressEnergyD2 P hP1 ν hν μ hγ w
  set s := Real.sqrt (∑ j, ‖g' j‖ ^ 2)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = ∑ j, ‖g' j‖ ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)
  set a := μ.re + 1 / 4
  set x := ‖(w : Yq P 2)‖
  set T := ‖smoothTensor P G‖
  have hT0 : 0 ≤ T := norm_nonneg _
  have hx0 : 0 ≤ x := norm_nonneg _
  have hinner : (inner ℂ (bodyOp P ν 2 μ w) (w : Yq P 2)).re ≤ T * s := by
    rw [hsol]
    exact tensorDivPairingLe P G hG hs _ g' hg'
  have hA : a * x ^ 2 + ν * s ^ 2 ≤ T * s := by
    rw [hs2]; linarith
  have hr : 0 < Real.sqrt (a * ν) := Real.sqrt_pos.2 (mul_pos hγ hν)
  have hr2 : Real.sqrt (a * ν) ^ 2 = a * ν := Real.sq_sqrt (mul_pos hγ hν).le
  rw [le_div_iff₀ (by positivity)]
  by_contra hcon
  rw [not_le] at hcon
  have h1 : T ^ 2 < (x * (2 * Real.sqrt (a * ν))) ^ 2 := by nlinarith
  have h2 : (x * (2 * Real.sqrt (a * ν))) ^ 2 = 4 * a * ν * x ^ 2 := by
    calc (x * (2 * Real.sqrt (a * ν))) ^ 2 = 4 * Real.sqrt (a * ν) ^ 2 * x ^ 2 := by ring
      _ = 4 * a * ν * x ^ 2 := by rw [hr2]; ring
  have h3 : 0 ≤ (2 * ν * s - T) ^ 2 := sq_nonneg _
  nlinarith

/-- Norm bound for `RepsVec G` on a real smooth tensor test `m`. -/
private theorem norm_RepsVec_real_le {ν ε c P : ℝ} [Fact (0 < P)]
    (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) (hP1 : P ≤ 1)
    {μ : ℂ} (hγ : 0 < μ.re + 1 / 4)
    (m : Chart → Ten3) (hm : IsTensorTest c (fun p => tv4 (m p)))
    (F : HTSpace c) (hF : (F : Profile → TensorVal) =ᵐ[measureHT c] (fun p => tv4 (m p)))
    (G : HSpace c MeridC)
    (hG : (G : Profile → MeridC) =ᵐ[measureH c]
      (fun p => (p.1 : ℂ) • divEps ε (fun q => tv4 (m q)) p)) :
    ‖UnforcedLeray.B0223.RepsVec hν hε hc hP μ G‖ ≤
      (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖ := by
  obtain ⟨U, hUl⟩ := N01.phaseLiftExists ε P hε
  obtain ⟨hTest, hM, hConj⟩ := liftVec_RepsVec_real hν hε hc hP hγ m hm G hG
  obtain ⟨hrows, hsym⟩ := N01.cartLiftRows ε c P hε hc hP m hm
  have h1 : (1 : ℝ≥0∞) < 2 := ENNReal.one_lt_two
  have h3 : (2 : ℝ≥0∞) < 3 := by norm_num
  have hμ' : 0 < μ.re + gammaR 2 := by rw [gammaR_two]; exact hγ
  obtain ⟨Rm, -, hRm⟩ := bodyResolvent_exists 2 h1 h3 P ν hν μ hμ'
  set g := testElem P 2 (tensorDiv (N01.cartRowsC (cartLift ε⁻¹ c m)))
  have hPhase : U (UnforcedLeray.B0223.liftVec hε hc hP
      (UnforcedLeray.B0223.RepsVec hν hε hc hP μ G)) =
      (((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) : ℝ) : ℂ) • Rm g := by
    rw [hConj, map_smul, N01.phaseLift_physRes N01.phaseSemigroupConj hν hε hUl hγ Rm _ hRm,
      N01.phaseDivScale ε c P hε hc hP U hUl _ hTest hM, map_smul, smul_smul]
    congr 1
    push_cast
    ring
  obtain ⟨v, hv, hvb⟩ := N01.bodyResolvent_bodyOp hP1 hν hγ Rm _ hRm g
  have hv_le : ‖Rm g‖ ≤
      ‖smoothTensor P (N01.cartRowsC (cartLift ε⁻¹ c m))‖ /
        (2 * Real.sqrt ((μ.re + 1 / 4) * ν)) := by
    rw [← hv]
    exact bodyOp_div_norm_le hP1 hν hγ v _ hrows hsym hvb
  have hnorm : ‖UnforcedLeray.B0223.RepsVec hν hε hc hP μ G‖ =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) * ‖Rm g‖ := by
    rw [← (UnforcedLeray.B0223.liftVec hε hc hP).norm_map, ← U.norm_map, hPhase,
      norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hNm := N01.cartLiftNorm ε c P hε hc hP m hm F hF
  set a := Real.sqrt ((μ.re + 1 / 4) * ν)
  have ha : 0 < a := Real.sqrt_pos.2 (mul_pos hγ hν)
  have hpos2π : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  rw [hnorm]
  calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) * ‖Rm g‖
      ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (P * ε) *
          (‖smoothTensor P (N01.cartRowsC (cartLift ε⁻¹ c m))‖ / (2 * a)) := by gcongr
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
          (Real.sqrt (P * ε) * ‖smoothTensor P (N01.cartRowsC (cartLift ε⁻¹ c m))‖) / (2 * a) := by
        ring
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi) * Real.sqrt 2 * ‖F‖) /
          (2 * a) := by gcongr
    _ = Real.sqrt 2 / 2 * (a⁻¹ * ‖F‖) := by field_simp
    _ ≤ 1 * (a⁻¹ * ‖F‖) := by gcongr; linarith
    _ = a⁻¹ * ‖F‖ := one_mul _

/-- Norm bound for `RepsVec G` on a complex smooth tensor test `M`. -/
private theorem norm_RepsVec_complex_le {ν ε c P : ℝ} [Fact (0 < P)]
    (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c) (hP1 : P ≤ 1)
    {μ : ℂ} (hγ : 0 < μ.re + 1 / 4)
    (M : Profile → TensorVal) (hM : IsTensorTest c M)
    (F : HTSpace c) (G : HSpace c MeridC)
    (hF : (F : Profile → TensorVal) =ᵐ[measureHT c] M)
    (hG : (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps ε M p)) :
    ‖UnforcedLeray.B0223.RepsVec hν hε hc hP μ G‖ ≤
      2 * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖ := by
  obtain ⟨m₁, m₂, hm₁, hm₂, -, hn₁, hn₂, hdiv⟩ := N01.tensorTestReIm c hc M hM
  have hMLp : MemLp M 2 (measureHT c) := (Lp.memLp F).ae_eq hF
  have hL₁ : MemLp (fun p => tv4 (m₁ p)) 2 (measureHT c) :=
    hMLp.of_le hm₁.smooth.continuous.aestronglyMeasurable (Eventually.of_forall hn₁)
  have hL₂ : MemLp (fun p => tv4 (m₂ p)) 2 (measureHT c) :=
    hMLp.of_le hm₂.smooth.continuous.aestronglyMeasurable (Eventually.of_forall hn₂)
  have hF₁n : ‖hL₁.toLp _‖ ≤ ‖F‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hL₁.coeFn_toLp, hF] with p h1 h2
    rw [h1, h2]
    exact hn₁ p
  have hF₂n : ‖hL₂.toLp _‖ ≤ ‖F‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hL₂.coeFn_toLp, hF] with p h1 h2
    rw [h1, h2]
    exact hn₂ p
  have hG₁L := UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c ε hc _ hm₁
  have hG₂L := UnforcedLeray.Short.PartIIIb.NearInst.Masked.tensorTestDivMem c ε hc _ hm₂
  have hGsplit : G = hG₁L.toLp _ + Complex.I • hG₂L.toLp _ := by
    apply Lp.ext
    filter_upwards [hG, hG₁L.coeFn_toLp, hG₂L.coeFn_toLp,
      Lp.coeFn_add (hG₁L.toLp _) (Complex.I • hG₂L.toLp _),
      Lp.coeFn_smul Complex.I (hG₂L.toLp _)] with p h h1 h2 h3 h4
    rw [h, h3, Pi.add_apply, h4, Pi.smul_apply, h1, h2, hdiv ε p, smul_add,
      smul_comm (p.1 : ℂ) Complex.I]
  have hb₁ := norm_RepsVec_real_le hν hε hc hP hP1 hγ m₁ hm₁ _
    hL₁.coeFn_toLp _ hG₁L.coeFn_toLp
  have hb₂ := norm_RepsVec_real_le hν hε hc hP hP1 hγ m₂ hm₂ _
    hL₂.coeFn_toLp _ hG₂L.coeFn_toLp
  set a := (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹
  have ha : 0 ≤ a := by positivity
  rw [hGsplit, map_add, map_smul]
  calc ‖UnforcedLeray.B0223.RepsVec hν hε hc hP μ (hG₁L.toLp _) +
          Complex.I • UnforcedLeray.B0223.RepsVec hν hε hc hP μ (hG₂L.toLp _)‖
      ≤ ‖UnforcedLeray.B0223.RepsVec hν hε hc hP μ (hG₁L.toLp _)‖ +
          ‖Complex.I • UnforcedLeray.B0223.RepsVec hν hε hc hP μ (hG₂L.toLp _)‖ := norm_add_le _ _
    _ = ‖UnforcedLeray.B0223.RepsVec hν hε hc hP μ (hG₁L.toLp _)‖ +
          ‖UnforcedLeray.B0223.RepsVec hν hε hc hP μ (hG₂L.toLp _)‖ := by
        rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ a * ‖hL₁.toLp _‖ + a * ‖hL₂.toLp _‖ := add_le_add hb₁ hb₂
    _ ≤ a * ‖F‖ + a * ‖F‖ := by gcongr
    _ = 2 * a * ‖F‖ := by ring

end UnforcedLeray.Short.PartIIa.N04SymGradAux

namespace UnforcedLeray.Short.PartIIa

/-- **Proof of `SymGradAdjointBound`** (source lines 1848–1860). -/
theorem symGradAdjointBound : SymGradAdjointBound := by
  refine ⟨2, by norm_num, ?_⟩
  intro ν c M γs hν hc hγs ε hε _ P _ hP hP1 μ hμM hμγ R Mtest F G hMt hF hG
  have hγ : 0 < μ.re + 1 / 4 := lt_of_lt_of_le hγs hμγ
  rw [ContinuousLinearMap.adjoint_inner_right]
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (UnforcedLeray.B0223.RepsVec hν hε hc hP μ G) R
  have h2 := N04SymGradAux.norm_RepsVec_complex_le hν hε hc hP hP1 hγ Mtest hMt F G hF hG
  have h3 := N01.inv_sqrt_le_window hν hγs hμM hμγ
  have h4 : 2 * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖ ≤
      2 * (1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ)) * ‖F‖ := by
    have h3' : 2 * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ ≤
        2 * (1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ)) := by
      linarith [mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ 2 by norm_num)]
    exact mul_le_mul_of_nonneg_right h3' (norm_nonneg F)
  calc ‖inner ℂ (UnforcedLeray.B0223.RepsVec hν hε hc hP μ G) R‖
      ≤ ‖UnforcedLeray.B0223.RepsVec hν hε hc hP μ G‖ * ‖R‖ := h1
    _ ≤ (2 * (Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹ * ‖F‖) * ‖R‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg R)
    _ ≤ (2 * (1 + M + γs⁻¹) * ν ^ (-(1 / 2 : ℝ)) * ‖F‖) * ‖R‖ :=
        mul_le_mul_of_nonneg_right h4 (norm_nonneg R)

end UnforcedLeray.Short.PartIIa
