import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.Comm
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEWeak
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEHess
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8.G1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8.G3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_4_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5.Rep

/-!
# Decomposition of `BgCorrHessEq` (source 2525-2562, 1351-1362, 1415-1424, 1515-1531)

Organizer item `ORG:ward/bg-bootstrap`, task `PartIII-b:C/ward/12/3/2/2`.  Source of record
`the November 2 reference manuscript`.

The second step of the bootstrap (2552-2559, induction step at `k = 1`): `∂_lg_j = k_{jl}` solves
`A₀k_{jl} = k_{jl} + ∂_l∂_j f - ∂_l∂_j𝐏(V·∇w + w·∇V + w·∇w)` with every term in `Y_p`.  It is
obtained without replicating the tree of `BgCorrGradEq`:

* the first-order equation is used in the functional form of `GEWeak` (2533-2537): on solenoidal
  tests `⟪L₀ᵗΨ, D_jw⟫ = ½⟪Ψ, D_jw⟫ + R_j(Ψ)`, `R_j(Ψ) = ⟪∂_jΨ, gF⟫ + ⟪∂_jΨ, gQ⟫ +
  ⟪conv_raw ∂_jΨ, w⟫ + ∑ᵢ αᵢ(⟪L₀ᵗ∂_jΨ, Eᵢ⟫ + ⟪conv_raw ∂_jΨ, Eᵢ⟫)`.  The parts of the first-order
  right side are determined only on solenoidal tests (`RawRel`, `QuadRel`, `GERaw`, …), i.e. modulo
  gradients; so the second-order statements are stated on `R_j(∂_lΦ)` itself, and are thereby
  independent of the representatives `Fr, Fq, Fl, Fᵢ` of `bgCorrGradEq_of`.  (`BgCorrGradEq`
  against all phase tests has the right side `𝐏F_j`, not `F_j`, so it is not used.)
* the commutator `HessComm.l0T_dy_fun` (`[∂_l, A₀] = ½∂_l`, 2529-2534) with `c = ½` gives
  `⟪L₀ᵗΦ, k_{jl}⟫ = ⟪Φ, k_{jl}⟫ - R_j(∂_lΦ)` on solenoidal tests;
* the four leaves state `R_j(∂_lΦ) = ⟪Φ, F⟫` part by part, `F ∈ Y_p` (2542-2551 complete sources in
  `W^{2,Y_p}`; 2555-2559 one factor of each order-2 derivative in `L^∞`, the other in `Y_p`):
  `RawResidualDeriv2Y` (raw residual), `GEInletIBP2` (inlet columns), `GELin2` (`B_raw w`),
  `GEQuad2` (`(e + w)·∇(e + w)`);
* `D³w ∈ Y_p` is `FreeGraphHessian` (1415-1424, the `GEHess` argument for any element of `D_p`)
  applied to `g_j ∈ D_p`; `w, Dw ∈ L^∞` come from `g_j ∈ D_p` (`bgContRepGraph`, 1515-1531);
* the solenoidal identity is lifted to all phase tests as in `gELift_of` (1358-1359, 1393-1400):
  `k_{jl}` is solenoidal (`∂_l` of the solenoidal `g_j`), and uniqueness on the solenoidal sector
  (`GEBodyUniqueSol`) identifies `k_{jl}` with the projected solution, right side `𝐏F`.
-/

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep)

/-! ## The leaves -/

/-- **(leaf 1) Second derivatives of the raw residual lie in `Y_{q₀}`** (source 2542-2551 at
`k = 2`: "the train and inlet complete sources belong to the corresponding `W^{k,Y_p}`. Explicitly,
in the large-radius region their unprojected derivatives are bounded by
`C_{k,N}ϱ^{-3-k}(1+|y₃|/ϱ)^{-N}`, whose `p`th integral reduces to `C∫_R^∞ϱ^{2-p(3+k)}dϱ < ∞`. On
`ϱ < R`, take the all-age heat expansion to a sufficiently high finite order: its even radial powers
extend smoothly through the axis"; `F_R = s^{3/2}r`, 1219-1225).  For the BUC train, `c = ν⁻²`,
`R ≥ 2`, `ν` small and period `≤ 1`, and all `j, l`, there is `G ∈ Y_{q₀}` (`G = ∂_l∂_jF_R`) with
`⟪∂_l∂_jΦ, F_R⟫ = ⟪Φ, G⟫` for every solenoidal phase test (the order-2 analogue of
`RawResidualDerivY`). -/
def RawResidualDeriv2Y : Prop :=
  ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ p : Params, UnforcedLeray.Short.PartI.IsBUCTrain p.train → p.ν < ν₀ →
    p.c = (p.ν ^ 2)⁻¹ → 2 ≤ p.R → p.period ≤ 1 → ∀ j l : Fin 3,
      ∃ G : Yq p.period UnforcedLeray.B0412.q0E, ∀ Φ, IsSolTest p.period Φ →
        pairF p.period (dy l (dy j Φ)) (UnforcedLeray.Short.IIb.rawResidualC p) =
          phasePair p.period UnforcedLeray.B0412.q0E Φ G

/-- **(leaf 2) Inlet columns at second order** (source 2542-2551 at `k = 2`: the inlet complete
source `L₀Eᵢ + B_rawEᵢ` is in `W^{2,Y_p}`; "the inlet cutoff vanishes near the axis. These estimates
are uniform in phase"; inlet jets 2385-2387, decay 2563-2569; `U_raw ∈ W^{3,∞}`, 1217-1219,
1322-1325): for each column `i` and `j, l` a pointwise field `F_n ∈ L^{q₀}` of the period cell
(`F_n = ∂_l∂_j(L₀Eᵢ + B_rawEᵢ)`) with
`⟪L₀ᵗ∂_l∂_jΦ, Eᵢ⟫ + ⟪conv_raw ∂_l∂_jΦ, Eᵢ⟫ = ⟪Φ, F_n⟫` on solenoidal tests (the order-2 analogue of
`GEInletIBP`). -/
def GEInletIBP2 : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j l : Fin 3), ∃ Fn : ℝ × UnforcedLeray.Space → CVec3,
    MemLp Fn UnforcedLeray.B0412.q0E
        ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) ∧
    ∀ Φ, IsSolTest p.period Φ →
      pairF p.period (UnforcedLeray.B0411.L0T p.ν (dy l (dy j Φ))) (p.Efun i) +
          pairF p.period (convT p.raw (dy l (dy j Φ))) (p.Efun i) = pairF p.period Φ Fn

/-- **(leaf 3) Linear term at second order** (source 2552-2559 at `k = 1`: "derivatives through
order `k+2` are in `Y_p`", so `w, Dw, D²w, D³w ∈ Y_p`; `U_raw ∈ W^{3,∞}`, 1217-1219, 1322-1325,
`RawSmoothBdd3`): with the Hessian `k_{jl} = ∂_lg_j` and the third derivatives
`t_{jlm} = ∂_mk_{jl}` in `Y_p`, `⟪conv_raw ∂_l∂_jΦ, w⟫ = ⟪Φ, F⟫` on solenoidal tests with `F ∈ Y_p`
(`F = ∂_l∂_j(B_raw w)`, `B_V h = V·∇h + h·∇V`). -/
def GELin2 : Prop := GERegime fun p z g =>
  ∀ (k : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (t : Fin 3 → Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E),
    (∀ j l : Fin 3, HasPhaseOp (fun Φ => -dy l Φ) (g j) (k j l)) →
    (∀ j l m : Fin 3, HasPhaseOp (fun Φ => -dy m Φ) (k j l) (t j l m)) →
    ∀ j l : Fin 3, ∃ F : Yq p.period UnforcedLeray.B0412.q0E, ∀ Φ, IsSolTest p.period Φ →
      pairF p.period (convT p.raw (dy l (dy j Φ))) (fun x => rep (p.wOf z) x.1 x.2) =
        phasePair p.period UnforcedLeray.B0412.q0E Φ F

/-- **(leaf 4) Quadratic term at second order** (source 2552-2559 at `k = 1`: "if derivatives
through order `k` are in the graph, all factors through order `k` are bounded and derivatives
through order `k+2` are in `Y_p`. In each order-`(k+1)` derivative of `w·∇w`, one factor has order
at most `k`. Put it in `L^∞` and the other in `Y_p`"; `w, Dw ∈ L^∞` from `w, g_j ∈ D_p` by
`bg:supremum-embedding`, 1515-1531, `bgContRepGraph`; inlet `e = E_εα` with jets of order `3`,
2385-2387): if every `g_j ∈ D_p`, with `k_{jl} = ∂_lg_j` and `t_{jlm} = ∂_mk_{jl}` in `Y_p`, then for
every `gQ` with `QuadRel z z gQ` (`gQ = 𝐏((e+w)·∇(e+w))`) and all `j, l` there is `F ∈ Y_p` with
`⟪∂_l∂_jΦ, gQ⟫ = ⟪Φ, F⟫` on solenoidal tests. -/
def GEQuad2 : Prop := GERegime fun p z g =>
  (∀ j : Fin 3, g j ∈ UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E) →
  ∀ (k : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (t : Fin 3 → Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E),
    (∀ j l : Fin 3, HasPhaseOp (fun Φ => -dy l Φ) (g j) (k j l)) →
    (∀ j l m : Fin 3, HasPhaseOp (fun Φ => -dy m Φ) (k j l) (t j l m)) →
    ∀ gQ : Yq p.period UnforcedLeray.B0412.q0E, p.QuadRel z z gQ → ∀ j l : Fin 3,
      ∃ F : Yq p.period UnforcedLeray.B0412.q0E, ∀ Φ, IsSolTest p.period Φ →
        phasePair p.period UnforcedLeray.B0412.q0E (dy l (dy j Φ)) gQ =
          phasePair p.period UnforcedLeray.B0412.q0E Φ F

/-! ## Raw and inlet parts in `Y_p` form -/

/-- **Raw part at second order** (source 2542-2551): for every `gF` with `RawRel gF` and all
`j, l` there is `F ∈ Y_p` with `⟪∂_l∂_jΦ, gF⟫ = ⟪Φ, F⟫` on solenoidal tests. -/
def GERaw2 : Prop := GERegime fun p _ _ =>
  ∀ gF : Yq p.period UnforcedLeray.B0412.q0E, p.RawRel gF → ∀ j l : Fin 3,
    ∃ F : Yq p.period UnforcedLeray.B0412.q0E, ∀ Φ, IsSolTest p.period Φ →
      phasePair p.period UnforcedLeray.B0412.q0E (dy l (dy j Φ)) gF =
        phasePair p.period UnforcedLeray.B0412.q0E Φ F

/-- **Inlet part at second order** (source 2542-2551): the derivative `∂_l∂_j` of the inlet
columns' contribution is in `Y_p`. -/
def GEInlet2 : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (j l : Fin 3), ∃ F : Yq p.period UnforcedLeray.B0412.q0E,
    ∀ Φ, IsSolTest p.period Φ →
      pairF p.period (UnforcedLeray.B0411.L0T p.ν (dy l (dy j Φ))) (p.Efun i) +
          pairF p.period (convT p.raw (dy l (dy j Φ))) (p.Efun i) =
        phasePair p.period UnforcedLeray.B0412.q0E Φ F

/-- `GERaw2` from the weak identity of the raw residual (2042-2046) and leaf 1, as in
`rawDerivRes_of`. -/
theorem gERaw2_of (h₁ : UnforcedLeray.Short.IIb.RawResidualWeakIdentity)
    (h₂ : RawResidualDeriv2Y) : GERaw2 := by
  obtain ⟨ν₁, hν₁, H1⟩ := h₁
  obtain ⟨ν₂, hν₂, H2⟩ := h₂
  intro lam q _ dm dp hdm
  refine ⟨min (min (ν₁ / 2) (ν₂ / 2)) (min dm (dm ^ 3 / 12)), ?_, ?_⟩
  · have : 0 < dm ^ 3 / 12 := by positivity
    positivity
  intro p d hreg hν _ z g _ gF hF j l
  have hνa : p.ν ≤ ν₁ / 2 := (hν.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hνb : p.ν ≤ ν₂ / 2 := (hν.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hνc : p.ν ≤ dm := (hν.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hνd : p.ν ≤ dm ^ 3 / 12 := (hν.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hR := two_le_R_of_regime hreg hνc
  have hP := bgCorr_period_le_one hreg hνd
  obtain ⟨G, hG⟩ := H2 p hreg.train_buc (by linarith) hreg.c_eq hR hP j l
  refine ⟨G, fun Φ hΦ => ?_⟩
  have hΨ : IsSolTest p.period (dy l (dy j Φ)) := gEW_isSolTest_dy (gEW_isSolTest_dy hΦ j) l
  rw [hF _ hΨ, H1 p hreg.train_buc (by linarith) hreg.c_eq hR _ hΨ]
  exact hG Φ hΦ

/-- `GEInlet2` from leaf 2 and `inletRepYq`, as in `gEInlet_of`. -/
theorem gEInlet2_of (h : GEInletIBP2) : GEInlet2 := by
  intro lam q hq dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h lam q hq dm dp hdm
  refine ⟨ν₀, hν₀, fun p d hreg hν hm z g hg i j l => ?_⟩
  obtain ⟨Fn, hFn, hid⟩ := H p d hreg hν hm z g hg i j l
  obtain ⟨F, hF⟩ := inletRepYq p.period Fn hFn
  refine ⟨F, fun Φ hΦ => ?_⟩
  rw [hid Φ hΦ, UnforcedLeray.Cons.C03.Concrete.phasePair_eq_pairF_rep hΦ.1 F]
  unfold pairF UnforcedLeray.Cons.C03.Concrete.phaseInt
  congr 1
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  filter_upwards [(ae_restrict_iff' measurableSet_Ioc).1 hF] with t ht' ht
  refine integral_congr_ae ?_
  filter_upwards [ht' ht] with y hy
  rw [hy]

/-! ## Solenoidality, lift and `D³w` -/

namespace HessEqSub

/-- `∂_l` of a solenoidal element is solenoidal (`⟪∇φ, ∂_lu⟫ = ⟪∇(-∂_lφ), u⟫ = 0`). -/
theorem mem_Ysigma_of_dy {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)] {u v : Yq P q}
    (l : Fin 3) (hu : u ∈ UnforcedLeray.B0411.Ysigma P q)
    (huv : HasPhaseOp (fun Φ => -dy l Φ) u v) : v ∈ UnforcedLeray.B0411.Ysigma P q := by
  rw [UnforcedLeray.B0411.mem_Ysigma] at hu ⊢
  intro φ hφ
  have h1 : phasePair P q (-dy l (gradT φ)) u = phasePair P q (gradT φ) v :=
    huv (gradT φ) hφ.gradT
  have h2 : -dy l (gradT φ) = -gradT (dy l φ) := by
    rw [g1_dy_gradT hφ.smooth l]
  have h3 : phasePair P q (gradT (dy l φ)) u = 0 := hu (dy l φ) (hφ.dy l)
  rw [h2, phasePair_neg (hφ.dy l).gradT, h3, neg_zero] at h1
  exact h1.symm

/-- **Lift from solenoidal tests** (source 1358-1359, 1393-1400; the argument of `gELift_of` for
any solenoidal `u`): if `⟪L₀ᵗΦ, u⟫ = ⟪Φ, F⟫` on solenoidal tests, then `A₀u = 𝐏F` against all
phase tests. -/
theorem solLift_of (h2 : GEBodyUniqueSol) (P ν : ℝ) [Fact (0 < P)] (hP : P ≤ 1) (hν : 0 < ν)
    (u F : Yq P UnforcedLeray.B0412.q0E)
    (huσ : u ∈ UnforcedLeray.B0411.Ysigma P UnforcedLeray.B0412.q0E)
    (hF : ∀ Φ, IsSolTest P Φ →
      phasePair P UnforcedLeray.B0412.q0E (UnforcedLeray.B0411.L0T ν Φ) u =
        phasePair P UnforcedLeray.B0412.q0E Φ F) :
    HasPhaseOp (fun Φ => (0 : ℂ) • Φ + UnforcedLeray.B0411.L0T ν Φ) u
      (UnforcedLeray.RieszLp.lerayY P UnforcedLeray.B0412.q0E q0E_gt_one
        (ne_top_of_lt q0E_lt_three) F) := by
  obtain ⟨w, hwσ, hw⟩ := UnforcedLeray.Short.PartIIa.commonBodyProjected
    UnforcedLeray.B0412.q0E q0E_gt_one q0E_lt_three P hP ν hν 0
    (by simpa using gammaR_q0E_pos) F
  have hL : UnforcedLeray.B0411.L0D w = UnforcedLeray.RieszLp.lerayY P UnforcedLeray.B0412.q0E
      q0E_gt_one (ne_top_of_lt q0E_lt_three) F := by
    simpa [UnforcedLeray.Short.PartIIa.bodyOp, UnforcedLeray.B0411.L0L_apply] using hw
  have hv : u - (w : Yq P UnforcedLeray.B0412.q0E) = 0 := by
    refine h2 P ν hP hν _ (Submodule.sub_mem _ huσ hwσ) ?_
    intro Φ hΦ
    rw [map_sub, hF Φ hΦ, UnforcedLeray.B0411.hasPhaseOp_L0D w Φ hΦ.1, hL,
      gELerayPairSol_proof P F Φ hΦ, sub_self]
  have hgu : u = (w : Yq P UnforcedLeray.B0412.q0E) := sub_eq_zero.1 hv
  intro Φ hΦ
  simp only [zero_smul, zero_add]
  rw [hgu, ← hL]
  exact UnforcedLeray.B0411.hasPhaseOp_L0D w Φ hΦ

/-- `FreeGraphHessian` (source 1415-1424): the composition of the accepted window leaves used by
`gEHess`. -/
theorem freeGraphHessian_thm : FreeGraphHessian :=
  freeGraphHessian_of (bodyHessianBound_of
    (localWindowHess_of windowBackHess)
    (globalHessFieldWindowBound_of windowHessAEMeas windowHessUnique windowHessPoU
      (windowHessPeriodic_of windowHessUnique))
    (hessFieldToYRep_of windowTestIdentityHess))

end HessEqSub

/-! ## The reduction -/

/-- **`BgCorrHessEq` from the four second-order parts** and uniqueness on the solenoidal sector
(source 2525-2562): `GEWeak` at the solenoidal test `∂_lΦ` and the commutator
`HessComm.l0T_dy_fun` give `⟪L₀ᵗΦ, k_{jl}⟫ = ⟪Φ, k_{jl}⟫ - R_j(∂_lΦ)`; the leaves write
`R_j(∂_lΦ) = ⟪Φ, F_r + F_q + F_l + ∑ᵢαᵢFᵢ⟫`; `solLift_of` lifts to all phase tests. -/
theorem bgCorrHessEq_of (hU : GEBodyUniqueSol) (h1 : GERaw2) (h2 : GEInlet2) (h3 : GELin2)
    (h4 : GEQuad2) : BgCorrHessEq := by
  intro lam q hq dm dp hdm
  obtain ⟨n0, hn0, H0⟩ := gEWeak lam q hq dm dp hdm
  obtain ⟨n1, hn1, H1⟩ := h1 lam q hq dm dp hdm
  obtain ⟨n2, hn2, H2⟩ := h2 lam q hq dm dp hdm
  obtain ⟨n3, hn3, H3⟩ := h3 lam q hq dm dp hdm
  obtain ⟨n4, hn4, H4⟩ := h4 lam q hq dm dp hdm
  have hn5 : 0 < dm ^ 3 / 12 := by positivity
  refine ⟨min (min (min n0 n1) (min n2 n3)) (min n4 (dm ^ 3 / 12)),
    lt_min (lt_min (lt_min hn0 hn1) (lt_min hn2 hn3)) (lt_min hn4 hn5), ?_⟩
  intro p d hreg hν hmode z hPE g hg k hk j l
  have e0 : p.ν ≤ n0 :=
    hν.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have e1 : p.ν ≤ n1 :=
    hν.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have e2 : p.ν ≤ n2 :=
    hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have e3 : p.ν ≤ n3 :=
    hν.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have e4 : p.ν ≤ n4 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e5 : p.ν ≤ dm ^ 3 / 12 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hP1 : p.period ≤ 1 := bgCorr_period_le_one hreg e5
  have hd : GEData p z (fun i => (g i : Yq p.period UnforcedLeray.B0412.q0E)) := ⟨hPE, hg⟩
  have hDmem : ∀ i : Fin 3, (g i : Yq p.period UnforcedLeray.B0412.q0E) ∈
      UnforcedLeray.B0411.D p.period p.ν UnforcedLeray.B0412.q0E := fun i => (g i).2
  -- third derivatives: `FreeGraphHessian` at each `g_a ∈ D_p` with gradient `k_a`
  obtain ⟨C, -, hB⟩ := HessEqSub.freeGraphHessian_thm UnforcedLeray.B0412.q0E q0E_gt_one
    q0E_lt_three
  have htex : ∀ a : Fin 3, ∃ h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E,
      ∀ b c : Fin 3, HasPhaseOp (fun Φ => -dy c Φ) (k a b) (h b c) := by
    intro a
    obtain ⟨h, hh, -⟩ := hB p.period hP1 p.ν p.ν_pos 0 (by simpa using gammaR_q0E_pos) (g a)
      (k a) (fun b => hk a b)
    exact ⟨h, hh⟩
  choose t ht using htex
  obtain ⟨gF, gL, gQ, hF, hL, hQ, hsum⟩ := hPE
  have W := H0 p d hreg e0 hmode z _ hd gF gL gQ hF hL hQ hsum j
  beta_reduce at W
  obtain ⟨Gr, hGr⟩ := H1 p d hreg e1 hmode z _ hd gF hF l j
  choose Gi hGi using fun i : Fin 2 => H2 p d hreg e2 hmode z _ hd i l j
  obtain ⟨Gl, hGl⟩ := H3 p d hreg e3 hmode z _ hd k t hk ht l j
  obtain ⟨Gq, hGq⟩ := H4 p d hreg e4 hmode z _ hd hDmem k t hk ht gQ hQ l j
  -- the twice differentiated equation on solenoidal tests
  have hsol : ∀ Φ, IsSolTest p.period Φ →
      phasePair p.period UnforcedLeray.B0412.q0E (UnforcedLeray.B0411.L0T p.ν Φ) (k j l) =
        phasePair p.period UnforcedLeray.B0412.q0E Φ
          (k j l - (Gr + Gq + Gl + ∑ i : Fin 2, (p.coord z i : ℂ) • Gi i)) := by
    intro Φ hΦ
    have key := HessComm.l0T_dy_fun (P := p.period) (q := UnforcedLeray.B0412.q0E) p.ν
      (IsSolTest p.period) (fun _ h => h.1) (fun _ h l' => gEW_isSolTest_dy h l') l (1 / 2 : ℂ)
      (fun Ψ => phasePair p.period UnforcedLeray.B0412.q0E (dy j Ψ) gF +
        phasePair p.period UnforcedLeray.B0412.q0E (dy j Ψ) gQ +
        pairF p.period (convT p.raw (dy j Ψ)) (fun x => rep (p.wOf z) x.1 x.2) +
        ∑ i : Fin 2, (p.coord z i : ℂ) *
          (pairF p.period (UnforcedLeray.B0411.L0T p.ν (dy j Ψ)) (p.Efun i) +
            pairF p.period (convT p.raw (dy j Ψ)) (p.Efun i)))
      (u := (g j : Yq p.period UnforcedLeray.B0412.q0E)) (v := k j l)
      (fun Ψ hΨ => by beta_reduce; rw [W Ψ hΨ]; ring) (hk j l) Φ hΦ
    beta_reduce at key
    rw [key, hGr Φ hΦ, hGq Φ hΦ, hGl Φ hΦ,
      Finset.sum_congr rfl (fun i _ => by rw [hGi i Φ hΦ])]
    simp only [map_sub, map_add, map_sum, map_smul, smul_eq_mul]
    ring
  have hgσ := gEGradSol_proof p z _ hd j
  have hkσ := HessEqSub.mem_Ysigma_of_dy l hgσ (hk j l)
  exact ⟨_, HessEqSub.solLift_of hU p.period p.ν hP1 p.ν_pos (k j l) _ hkσ hsol⟩

end UnforcedLeray.Short.PartIIIb.Concrete

#print axioms UnforcedLeray.Short.PartIIIb.Concrete.bgCorrHessEq_of
#print axioms UnforcedLeray.Short.PartIIIb.Concrete.gERaw2_of
#print axioms UnforcedLeray.Short.PartIIIb.Concrete.gEInlet2_of
#print axioms UnforcedLeray.Short.PartIIIb.Concrete.HessComm.hasPhaseOp_L0T_dy
