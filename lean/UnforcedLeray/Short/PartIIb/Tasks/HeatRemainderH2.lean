import UnforcedLeray.Short.PartIIb.Sub.PartIIb_B3_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_B3_2_1
import UnforcedLeray.Short.PartIIb.Sub.B3
import UnforcedLeray.Short.PartIIb.Compose
import UnforcedLeray.Short.PartIIb.Tasks.DatumFacts
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainderUL4
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainderEvol
import UnforcedLeray.Short.PartIIb.Tasks.StrongRegularity.JointSmooth
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainderH2.RawHeat
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainderH2.StressCont
import UnforcedLeray.Short.PartIIb.Tasks.HeatRemainderH2.FreeUniq
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison
import UnforcedLeray.Short.PartIIb.Tasks.QuadraticEstimate
import UnforcedLeray.Short.PartIIb.Tasks.StrongFirstDerivative
import UnforcedLeray.Short.PartIIb.Tasks.StrongHigherOrder

/-!
# `PartII-b:B3/2/1`: the heat remainder `Q = U − H_a ∈ C_τ H²` (`Tasks/HeatRemainderH2.lean`, SP 2584-2628)

Source of record: `the November 2 reference manuscript`, lines 2584-2628.

At every contraction-ball state `(p, z)` (quantifiers of `B3Stmt.AtBallStates`), with
`U = bgField p z`, `a = p.datum (p.coord z)`, and `H_a = Blueprint.heatProfile p.ν a`:
1. `StrongAllOrders` (`PartII-b:S2`) and the proved spacetime bootstrap
   (`jointSmoothnessFromSpatialAllOrders_proof`, `bgFirstOrderPhaseDeriv_proof`) give joint
   smoothness of `U`, `IsUniformSmoothL4SliceFamily U`, its comoving derivative `U₁` in
   `IsUniformSmoothL4SliceFamily`, and `D^jU ∈ C_per L⁴` for `j ≤ 2` (`ballHeatRemainder_UL4_of`);
2. `B3RemH2Sub.stressColH2` and `B3RemH2Sub.norm_stressColH2_le` construct the `H²(ℝ³)` columns
   `P_U(τ) = (U_m U)_{m < 3}` of `𝕋 = U ⊗ U` with uniform `H²` norm bound `43 * max C 0 ^ 2`,
   continuous in `τ` by `StressColsContinuousH2`, and satisfying `-𝐏 div 𝕋 = -𝐏(U·∇U)` for
   solenoidal `U` (`B3RemH2Sub.Xclass_minusLerayDivX_stressColH2`);
3. `B3RemH2Sub.freeStressDuhamelH2 p.ν P_U` defines `Q : ℝ → H²(ℝ³)` as the free similarity
   Duhamel integral `-∫₀^∞ S₀(r) 𝐏 div 𝕋(τ - r) dr`, proved continuous on `ℝ` in
   `B3RemH2Sub.continuous_freeStressDuhamelH2` via the short-time `r^{-1/2}` and long-time
   `e^{-r/4}` operator bounds of `S₀(r) : X → Z` (`B3RemH2Sub.freeDuhamelKernel`);
4. `RawHeatComparison` (`short-bg:raw-heat`, SP 2586-2603) combined with the graph-state bound
   `w ∈ L^{11/4}` (`B3RemH2Sub.remainder_eLpNorm_q0E_le`) and the remainder evolution
   (`ballHeatRemainder_Evol_of`) feeds free uniqueness on `Y_{11/4}` (`FreeDuhamelUniquenessAe`),
   identifying `(Q τ).value` with `U(τ) - H_a(τ)` at almost every phase `τ : ℝ`, and
   `B3RemH2Sub.ae_eq_every_phase_of_aem_phase` upgrades the identification to **every** phase `τ : ℝ`
   using `L⁴` slice continuity (`B3RemH2Sub.exists_continuous_bgField_L4`).

Main result: `ballRemainderH2_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.SobolevGraph

/-- **`PartII-b:B3/2/1` (`BallRemainderH2`)** assembled from `StrongAllOrders` (`PartII-b:S2`) and
the three sub-step leaves of `Sub/PartII-b_B3_2_1.lean` (`RawHeatComparison`,
`StressColsContinuousH2`, `FreeDuhamelUniquenessAe`). -/
theorem ballRemainderH2_of (hS2 : StrongAllOrders) (hRawHeat : RawHeatComparison)
    (hStressCont : StressColsContinuousH2) (hUniq : FreeDuhamelUniquenessAe) :
    BallRemainderH2 := by
  have hCombined := (ballHeatRemainder_UL4_of hS2).and
    ((ballHeatRemainder_Evol_of hS2).and (datum_facts_atBallStates.and hRawHeat))
  intro Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₁, hν₁, HS2⟩ := hS2 Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₂, hν₂, HJ⟩ :=
    jointSmoothnessFromSpatialAllOrders_proof Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₃, hν₃, HF⟩ :=
    bgFirstOrderPhaseDeriv_proof Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₄, hν₄, HC⟩ := hCombined Sig lam q hSig hq m hm dm dp hdm h2m C₁ k₁ hC₁
  obtain ⟨ν₅, hν₅, hper⟩ := poly_exp_small 2 dm 2 hdm
  refine ⟨min (min ν₁ ν₂) (min ν₃ (min ν₄ ν₅)),
    lt_min (lt_min hν₁ hν₂) (lt_min hν₃ (lt_min hν₄ hν₅)),
    fun p d hreg hν hS hq' z hz hzn => ?_⟩
  have hν₁' : p.ν ≤ ν₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₂' : p.ν ≤ ν₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν₃' : p.ν ≤ ν₃ := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hν₄' : p.ν ≤ ν₄ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hν₅' : p.ν ≤ ν₅ :=
    hν.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hgrad, hslice, hRaw, hInlet⟩ := HS2 p d hreg hν₁' hS hq' z hz hzn
  have hsmooth : ContDiff ℝ ∞ (fun x : ℝ × Space => bgField p z x.1 x.2) :=
    HJ p d hreg hν₂' hS hq' z hz hzn hgrad hslice hRaw hInlet
  obtain ⟨hBgFam, U₁, hU₁Fam, hU₁Deriv⟩ :=
    HF p d hreg hν₃' hS hq' z hz hzn hgrad hslice hRaw hInlet
  obtain ⟨⟨C, hUL4⟩, hEvol, ⟨hD, -, -, -⟩, ⟨⟨R_V, hRV_cont, hRV_ae⟩, ⟨M_V, hMV⟩⟩⟩ :=
    HC p d hreg hν₄' hS hq' z hz hzn
  have hP1 : p.period ≤ 1 := period_le_one_of hreg (hper p.ν p.ν_pos hν₅')
  obtain ⟨hperU, hsolU, -⟩ := bgField_periodic_solenoidal_symmetric p hP1 z hRaw hInlet
  have hf : ∀ τ : ℝ, ContDiff ℝ 2 (bgField p z τ) := fun τ => by
    simpa using hBgFam.slice_contDiff 2 τ
  have h0 : ∀ τ : ℝ, eLpNorm (bgField p z τ) 4 volume ≤ ENNReal.ofReal C := fun τ => (hUL4 τ).1
  have h1 : ∀ τ : ℝ, eLpNorm (fun y => fderiv ℝ (bgField p z τ) y) 4 volume ≤ ENNReal.ofReal C :=
    fun τ => (hUL4 τ).2.1
  have h2 : ∀ τ : ℝ, eLpNorm (fun y => iteratedFDeriv ℝ 2 (bgField p z τ) y) 4 volume ≤
      ENNReal.ofReal C := fun τ => (hUL4 τ).2.2
  let P_U : ℝ → Fin 3 → SobolevGraph.H2 :=
    fun τ m => B3RemH2Sub.stressColH2 (bgField p z τ) (hf τ) (h0 τ) (h1 τ) (h2 τ) m
  have hP_cont : Continuous P_U :=
    hStressCont (bgField p z) hsmooth hBgFam ⟨U₁, hU₁Fam, hU₁Deriv⟩ C hf h0 h1 h2
  have hP_bdd : ∃ B : ℝ, ∀ (τ : ℝ) (m : Fin 3), ‖P_U τ m‖ ≤ B :=
    ⟨43 * max C 0 ^ 2, fun τ m =>
      B3RemH2Sub.norm_stressColH2_le (bgField p z τ) (hf τ) (h0 τ) (h1 τ) (h2 τ) m⟩
  let Q : ℝ → SobolevGraph.H2 := B3RemH2Sub.freeStressDuhamelH2 p.ν P_U
  have hQ_cont : Continuous Q :=
    B3RemH2Sub.continuous_freeStressDuhamelH2 p.ν_pos hP_cont hP_bdd
  have hMq : ∃ M_q : ℝ, ∀ τ : ℝ,
      eLpNorm (bgField p z τ -
        UnforcedLeray.Blueprint.heatProfile p.ν (p.datum (p.coord z)) τ) B0412.q0E volume ≤
        ENNReal.ofReal M_q :=
    ⟨max M_V 0 + ‖z‖,
      B3RemH2Sub.remainder_eLpNorm_q0E_le p hP1 z hRaw.1 (fun i => (hInlet i).1) hD hMV⟩
  have hInt_aem := hUniq p.ν p.period p.ν_pos p.period_pos hP1 (p.datum (p.coord z)) hD
    (bgField p z) hsmooth hBgFam hperU hsolU hMq (fun τ => (hEvol τ).2)
  have hQ_val_eq : ∀ τ : ℝ, (Q τ).value =
      ∫ r in Ioi (0 : ℝ), Loc.L02.freeL2 p.ν r
        (-(UnforcedLeray.Leray.projection (UnforcedLeray.toL2
          (fun y => fderiv ℝ (bgField p z (τ - r)) y (bgField p z (τ - r) y))))) := by
    intro τ
    rw [B3RemH2Sub.value_freeStressDuhamelH2 p.ν_pos hP_cont hP_bdd τ]
    refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
    rw [B3RemH2Sub.minusLerayDivXCLM_apply,
      B3RemH2Sub.Xclass_minusLerayDivX_stressColH2 (bgField p z (τ - r)) (hf (τ - r))
        (hsolU (τ - r)) (h0 (τ - r)) (h1 (τ - r)) (h2 (τ - r))]
  have hQ_aem : ∀ᵐ τ : ℝ, ((Q τ).value : SpatialField) =ᵐ[volume]
      bgField p z τ - UnforcedLeray.Blueprint.heatProfile p.ν (p.datum (p.coord z)) τ := by
    filter_upwards [hInt_aem] with τ hτ
    rwa [← hQ_val_eq τ] at hτ
  obtain ⟨W_U, W_H, hWU_cont, hWH_cont, hWU_ae, hWH_ae⟩ :=
    B3RemH2Sub.exists_continuous_bgField_L4 p hP1 z hD hRV_cont hRV_ae
  exact ⟨Q, hQ_cont,
    B3RemH2Sub.ae_eq_every_phase_of_aem_phase hQ_cont hWU_cont hWH_cont hWU_ae hWH_ae hQ_aem⟩

theorem ballRemainderH2_proof : UnforcedLeray.Short.IIb.BallRemainderH2 := by
  have h4 := affineInletFacts_proof
  have hQ1 := quadBound_of h4
  exact ballRemainderH2_of (strongAllOrders_of h4 hQ1 (_root_.strongFirstDerivative_of h4 hQ1))
    rawHeatComparison_proof stressColsContinuousH2_proof freeDuhamelUniquenessAe_proof

end UnforcedLeray.Short.IIb

end
