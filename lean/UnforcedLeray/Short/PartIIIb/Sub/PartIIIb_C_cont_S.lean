import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Compose
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Seq
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Defs

/-!
# `PartIII-b:C/cont/S`: `S_μ` is norm continuous on the window (source 5701-5702, 1556-1583,
1675-1690, 3888-3890)

Source of record: `the November 2 reference manuscript` (73 pages).

On the window the pinned weak stress inverse is `stressG (Seps μ)`, `Seps μ = realForm (S'_μ)` the
real form of the complex stress map `S'_μ` of `T_ε(μ)` (uniqueness of weak stress inverses,
`FreeWeakUniqueness`, 1571, 1580-1583).  The one analytic input is that the complex stress maps
form a norm-continuous family in `μ` (`StressMapFamilyCont`: resolvent identity
`S'_μ - S'_μ' = (μ'-μ) R^{vec}(μ) S'_μ'`, `‖R^{vec}(μ)‖ ≤ (μ+1/4)⁻¹`, 1675-1690); the rest is
a fixed sandwich (`realForm`, `stressG`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Short.PartIIIb.NearInst
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-- **The stress maps `S'_μ` of `T_ε(μ)` form a norm-continuous family in real `μ > -1/4`**
(source 1556-1583, 1675-1690, 3888-3890: `S'_μ = T_ε(μ) s div_ε` completed from smooth tensors;
resolvent identity `S'_μ - S'_μ' = (μ'-μ) R^{vec}(μ) S'_μ'` on smooth tensors, hence everywhere by
density, with `‖R^{vec}(μ)‖ ≤ (μ + 1/4)⁻¹`), at a level with `ε ≤ 1` and `P = 2εc ≤ 1`. -/
def StressMapFamilyCont : Prop :=
  ∀ (p : UnforcedLeray.Cons.C03.Concrete.Params), p.ε ≤ 1 → p.period ≤ 1 →
    ∃ S' : ℝ → (UnforcedLeray.Short.PartIIa.HTSpace p.c →L[ℂ]
        UnforcedLeray.B0220.HSpace p.c UnforcedLeray.B0223.MeridC),
      ContinuousOn S' (Ioi (-(1 / 4 : ℝ))) ∧ ∀ μ : ℝ, -(1 / 4) < μ →
        UnforcedLeray.Short.PartIIa.IsStressMap p.c p.ε
          (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ))
          (S' μ)

/-- **Resolvent identity for stress maps** (source 1556-1583, 1675-1690, 3888-3890): if `S` and
`S'` are stress maps of `T_ε(μ)` and `T_ε(μ')` (real `μ, μ' > -1/4`), then
`S - S' = (μ' - μ) R^{vec}(μ) ∘ S'`.  (On smooth tensors, `S F - S' F = (T_ε(μ) - T_ε(μ')) G`
and `R^{vec}(μ) - R^{vec}(μ') = (μ' - μ) R^{vec}(μ) R^{vec}(μ')`; then by density.) -/
def StressMapResolvent : Prop :=
  ∀ (ν ε c P : ℝ) [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (μ μ' : ℝ), -(1 / 4) < μ → -(1 / 4) < μ' →
    ∀ S S' : UnforcedLeray.Short.PartIIa.HTSpace c →L[ℂ]
        UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
      UnforcedLeray.Short.PartIIa.IsStressMap c ε
        (UnforcedLeray.Short.PartIIa.Teps hν hε hc hP (μ : ℂ)) S →
      UnforcedLeray.Short.PartIIa.IsStressMap c ε
        (UnforcedLeray.Short.PartIIa.Teps hν hε hc hP (μ' : ℂ)) S' →
      S - S' = (((μ' - μ : ℝ) : ℂ)) •
        ((UnforcedLeray.B0223.RepsVec hν hε hc hP (μ : ℂ)) ∘L S')

/-- Free weak uniqueness at all admissible parameters (source 1571, 1580-1583; task
`PartIII-b:IIIb-D2/1`). -/
def FreeWeakUniquenessAll : Prop :=
  ∀ {c γ ν ε μ : ℝ}, 0 < c → 0 < ν → 0 < ε → 2 * ε * c ≤ 1 → 0 < μ + 1 / 4 →
    FreeWeakUniqueness c γ ν ε μ

/-- `μ ↦ stressG (Seps μ)` is continuous where `μ ↦ Seps μ` is (a fixed sandwich). -/
theorem stressG_continuousOn {c mZ ρb γ ν : ℝ} (hν : 0 < ν) {X : Type} [TopologicalSpace X]
    {s : Set X} {F : X → (Zsp c mZ ρb →L[ℝ] Hsp c)} (h : ContinuousOn F s) :
    ContinuousOn (fun x => stressG (F x) γ hν) s := by
  unfold stressG NearInst.NearOps.SNG NearInst.gainConjS
  refine ContinuousOn.fun_const_smul ?_ _
  refine continuousOn_sandwich _ _ ?_
  exact continuousOn_sandwich _ _ h

/-- `S' ↦ realForm S'` is a fixed sandwich of `S'.restrictScalars ℝ`. -/
theorem realForm_continuousOn {c mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb)
    (hT : NearInst.Masked.CellPtHT c) (hH : NearInst.Masked.CellPtInvH c) {X : Type}
    [TopologicalSpace X] {s : Set X}
    {S' : X → (UnforcedLeray.Short.PartIIa.HTSpace c →L[ℂ]
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC)} (h : ContinuousOn S' s) :
    ContinuousOn (fun x => NearInst.Masked.realForm c mZ ρb hmZ hρ hT hH (S' x)) s := by
  have hres : Continuous fun Y : (UnforcedLeray.Short.PartIIa.HTSpace c →L[ℂ]
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) => Y.restrictScalars ℝ :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ _ _ ℝ ℝ).continuous
  unfold NearInst.Masked.realForm
  exact continuousOn_const.clm_comp ((hres.comp_continuousOn h).clm_comp
    (continuousOn_const.clm_comp continuousOn_const))

/-- **`sopCont` from the source facts** (source 5701-5702, 1556-1583, 1675-1690, 3888-3890): with
the continuous family of complex stress maps (`StressMapFamilyCont`), their reality
(`Masked.StressMapReal`), the stress-map weak solution property (`NearInst.StressMapWeakSol`),
the pair identity (`NearInst.StressPairAE`), the cell recentrings and free weak uniqueness, the
pinned `Sop` is `stressG (realForm S'_μ)` on the window, hence continuous. -/
theorem sopCont_of (hF : StressMapFamilyCont) (hR : NearInst.Masked.StressMapReal)
    (hW : NearInst.StressMapWeakSol) (hPA : NearInst.StressPairAE)
    (hT : ∀ c : ℝ, 0 < c → NearInst.Masked.CellPtHT c)
    (hH : ∀ c : ℝ, 0 < c → NearInst.Masked.CellPtInvH c)
    (hH' : ∀ c : ℝ, 0 < c → NearInst.Masked.CellPtH c) (hFU : FreeWeakUniquenessAll)
    (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.SopCont := by
  filter_upwards [inv_seq_large D hst.dm_pos hst.omega_ne hst.sigma_pos hst.sigma_lt hst.actual,
    hst.pins] with n hn hp
  obtain ⟨-, hper, hε1', hμ⟩ := hn
  set L := D.level n with hLdef
  have hε1 : L.ε ≤ 1 := hε1'
  have hmZ : 0 ≤ D.K.mZ := by linarith [hst.mZ_gt]
  have hρ : 0 < L.ρb D.Pl D.K := inv_rhoB_pos hst.C0_pos
  have hwin : ∀ μ ∈ D.win n, -(1 / 4 : ℝ) < μ := by
    rintro _ ⟨z, hz, rfl⟩
    have := (hμ z hz).1
    linarith [hst.sigma_pos]
  obtain ⟨S', hSc, hS'⟩ := hF (L.params D.Pl) hε1 hper
  have hc := cOf_pos L.ν_pos
  have hcont : ContinuousOn (fun μ : ℝ => NearInst.Masked.realForm (cOf L.ν) D.K.mZ
      (L.ρb D.Pl D.K) hmZ hρ (hT _ hc) (hH _ hc) (S' μ)) (D.win n) :=
    realForm_continuousOn hmZ hρ (hT _ hc) (hH _ hc)
      (hSc.mono (fun μ hμ => hwin μ hμ : D.win n ⊆ Ioi _))
  have h2 := stressG_continuousOn (γ := gRate D.Pl) L.ν_pos hcont
  refine h2.congr fun μ hμ => ?_
  have hpin := (hp)
  obtain ⟨z, hz, rfl⟩ := hμ
  have hspec : IsWeakStressInverse (Sop D.Pl D.K L (D.mu n z)) L.ε (D.mu n z) :=
    Classical.epsilon_spec (hpin z hz).stress
  have hlt := hwin _ (D.mu_mem_win hz)
  have hreal := hR (L.params D.Pl).ν (L.params D.Pl).ε (L.params D.Pl).c (L.params D.Pl).period (L.params D.Pl).ν_pos (L.params D.Pl).ε_pos (L.params D.Pl).c_pos rfl
    (D.mu n z) hlt (S' (D.mu n z)) (hS' _ hlt)
  have htr := NearInst.Masked.isStressTransport_realForm (mZ := D.K.mZ) (ρb := L.ρb D.Pl D.K)
    hmZ hρ (hT _ hc) (hH _ hc) (hH' _ hc) (S' (D.mu n z)) hreal
  have hweak := isWeakStressInverse_stressG hW hPA hper hlt (gRate D.Pl) hmZ hρ
    (hS' _ hlt) htr
  exact eq_of_isWeakStressInverse (hFU hc L.ν_pos L.ε_pos hper
    (by linarith)) hspec hweak

end UnforcedLeray.Short.PartIIIb.Concrete
