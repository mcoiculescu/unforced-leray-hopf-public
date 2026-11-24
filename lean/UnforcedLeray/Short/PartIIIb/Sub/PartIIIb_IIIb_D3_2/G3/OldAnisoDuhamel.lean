import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G3.OldAnisoOrg
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.DuhamelUnif
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D3_2.G1.FrozenPairActual

/-!
# `PartIII-b:IIIb-D3/2/G3/1/1`: Duhamel decomposition at `H = 2/ν` (`G3.DuhamelDecomp`)

Source of record: `the November 2 reference manuscript` (lines 4461-4518, 4540-4543).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set MeasureTheory
open scoped ComplexConjugate

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3

open ConcreteYF

/-- **Leaf 1 (`G3/1/1`)**: Duhamel decomposition on `s ≥ 2/ν`, remainder bound and amplitude bound
(source 4461-4518, 4540-4543). -/
theorem duhamelDecomp_of (D : SeqData) (hSF : G1.YoungSourceFacts D) (hGBA : G1.GBAdmissible D) :
    G3.DuhamelDecomp D := by
  intro dm dp hst κ hκ m hfact hm S hS
  obtain ⟨N0, δ, ⟨Cb, hb⟩, -, -⟩ := hSF dm dp hst κ hκ m hm S hS
  obtain ⟨Cfp, Nfp, hCfp⟩ := G1.youngFrozenPair_actual D hSF dm dp hst κ hκ m hm S hS
  obtain ⟨Ngba, hA⟩ := hGBA dm dp hst κ hκ m hm S hS
  obtain ⟨Nact, hAct⟩ := eventually_atTop.1 hS
  set M := N0 + Nact
  have hL_shift : ∀ k, YoungLaws (S (k + M)).pk (S (k + M)).conjX := by
    intro k
    obtain ⟨FI, hFI⟩ := hAct (k + M) (by omega)
    rw [hFI]
    exact FlatSettingInst.youngLaws_actualPk FI
  have hHyp_shift : YoungHyp (fun k => nu D (k + M)) D.Pl.eigenvalue 2 1.1 := by
    refine ⟨fun k => retNu_pos D.Pl D.σ₀ (k + M), ?_, hst.gamma_pos, by norm_num, by norm_num⟩
    exact (retNu_tendsto (Pl := D.Pl) D.σ₀ hst.omega_ne).comp (tendsto_add_atTop_nat M)
  have hBd_shift : YoungBounded (fun k => (S (k + M)).pk) (fun k => nu D (k + M)) 2 :=
    ⟨Cb, fun k s hs j => hb (k + M) (by omega) s hs j⟩
  have hFP_shift : YoungFrozenPair (fun k => (S (k + M)).pk) (fun k => nu D (k + M))
      D.Pl.eigenvalue D.Pl.kappa 2 1.1 :=
    ⟨Cfp, Nfp, fun k hk t ht => hCfp (k + M) (by omega) t ht⟩
  obtain ⟨C0, Nduh, hDuh⟩ := G1.youngDuhamelUnif (fun k => (S (k + M)).pk)
    (fun k => (S (k + M)).conjX) (fun k => nu D (k + M)) D.Pl.eigenvalue D.Pl.kappa 2 1.1
    hL_shift hHyp_shift hBd_shift hFP_shift
  refine ⟨max C0 0, max Cb 0, Nduh + M + Ngba, le_max_right C0 0, le_max_right Cb 0, ?_⟩
  intro n hn z hz B hB
  obtain ⟨k, rfl⟩ : ∃ k, n = k + M := ⟨n - M, by omega⟩
  have hk_duh : Nduh ≤ k := by omega
  have hn_gba : Ngba ≤ k + M := by omega
  have hn_act : Nact ≤ k + M := by omega
  have hn_0 : N0 ≤ k + M := by omega
  obtain ⟨FI, hFI⟩ := hAct (k + M) hn_act
  have hL : YoungLaws (S (k + M)).pk (S (k + M)).conjX := hL_shift k
  have hν : 0 < nu D (k + M) := retNu_pos D.Pl D.σ₀ (k + M)
  have : Fact (0 < cOf (retNu D.Pl D.σ₀ (k + M))) := ⟨cOf_pos hν⟩
  have hreal : ∀ t, (S (k + M)).conjX ((S (k + M)).gB B t) = (S (k + M)).gB B t := by
    intro t
    rw [hFI]
    exact FlatSettingInst.gBD_real FI B t
  obtain ⟨hf_hi, hf_lo, hf_U, hf_A1, hf_A2, hf_W⟩ := hA (k + M) hn_gba z hz B hB
  have hTfH : 1.1 / nu D (k + M) ≤ 2 / nu D (k + M) :=
    div_le_div_of_nonneg_right (by norm_num) hν.le
  have h0H : 0 ≤ 2 / nu D (k + M) := div_nonneg (by norm_num) hν.le
  -- 1. Trajectory decomposition on `s ≥ 2 / nu D (k + M)`
  have h1 : ∀ s : ℝ, 2 / nu D (k + M) ≤ s →
      (S (k + M)).xi (D.mu (k + M) z : ℂ) B s =
        xiBare (S (k + M)) (D.mu (k + M) z)
          ((S (k + M)).aNuC D.Pl.eigenvalue D.Pl.kappa (D.mu (k + M) z : ℂ) (nu D (k + M)) B) s +
        xiFromH (S (k + M)) (nu D (k + M)) (D.mu (k + M) z) (duhRemH D (S (k + M)) (k + M) z B) s := by
    intro s hHs
    unfold FlatSetting.xi xiBare xiFromH
    rw [duhamel_cocycle_of_ge hL hTfH hHs hf_hi hf_U]
    have hsplit : duhamel (S (k + M)).pk (D.mu (k + M) z : ℂ) ((S (k + M)).gB B) (2 / nu D (k + M)) =
        bareCol (S (k + M))
          ((S (k + M)).aNuC D.Pl.eigenvalue D.Pl.kappa (D.mu (k + M) z : ℂ) (nu D (k + M)) B)
          (2 / nu D (k + M)) +
        duhRemH D (S (k + M)) (k + M) z B := by
      unfold duhRemH
      exact (add_sub_cancel _ _).symm
    rw [hsplit, map_add, uev_bareCol hL _ h0H hHs, smul_add]
  -- 2. Duhamel remainder bound at `H = 2 / nu D (k + M)`
  have h2 : ‖duhRemH D (S (k + M)) (k + M) z B‖ ≤
      max C0 0 * nu D (k + M) *
        ‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D (k + M)) (2 / nu D (k + M)) 0‖ *
        testedNorm (S (k + M)).pk D.Pl.eigenvalue D.Pl.kappa (nu D (k + M)) (D.mu (k + M) z : ℂ)
          (1.1 / nu D (k + M)) ((S (k + M)).gB B) := by
    have hconj_a : aFrozen (S (k + M)).pk false D.Pl.eigenvalue D.Pl.kappa (nu D (k + M))
        (D.mu (k + M) z : ℂ) (1.1 / nu D (k + M)) ((S (k + M)).gB B) =
        conj ((S (k + M)).aNuC D.Pl.eigenvalue D.Pl.kappa (D.mu (k + M) z : ℂ) (nu D (k + M)) B) :=
      aFrozen_false_eq_conj_of_real hL hν hreal
    have hbare_eq : bareCol (S (k + M))
        ((S (k + M)).aNuC D.Pl.eigenvalue D.Pl.kappa (D.mu (k + M) z : ℂ) (nu D (k + M)) B)
        (2 / nu D (k + M)) =
      aFrozen (S (k + M)).pk true D.Pl.eigenvalue D.Pl.kappa (nu D (k + M)) (D.mu (k + M) z : ℂ)
          (1.1 / nu D (k + M)) ((S (k + M)).gB B) •
        (S (k + M)).pk.Uev (2 / nu D (k + M)) 0 ((S (k + M)).pk.q true 0) +
      aFrozen (S (k + M)).pk false D.Pl.eigenvalue D.Pl.kappa (nu D (k + M)) (D.mu (k + M) z : ℂ)
          (1.1 / nu D (k + M)) ((S (k + M)).gB B) •
        (S (k + M)).conjX ((S (k + M)).pk.Uev (2 / nu D (k + M)) 0 ((S (k + M)).pk.q true 0)) := by
      unfold bareCol FlatSetting.aNuC
      rw [hconj_a]
      rfl
    have hraw := hDuh (D.mu (k + M) z : ℂ) k hk_duh ((S (k + M)).gB B)
      hf_hi hf_lo hf_U hf_A1 hf_A2 (by simpa using hf_W)
    have hrem : ‖duhRemH D (S (k + M)) (k + M) z B‖ ≤
        C0 * nu D (k + M) *
          ‖Fpm true D.Pl.eigenvalue D.Pl.kappa (nu D (k + M)) (2 / nu D (k + M)) 0‖ *
          testedNorm (S (k + M)).pk D.Pl.eigenvalue D.Pl.kappa (nu D (k + M)) (D.mu (k + M) z : ℂ)
            (1.1 / nu D (k + M)) ((S (k + M)).gB B) := by
      unfold duhRemH
      rw [hbare_eq]
      exact hraw
    have htn_nonneg : 0 ≤ testedNorm (S (k + M)).pk D.Pl.eigenvalue D.Pl.kappa (nu D (k + M))
        (D.mu (k + M) z : ℂ) (1.1 / nu D (k + M)) ((S (k + M)).gB B) := by
      unfold testedNorm
      refine setIntegral_nonneg measurableSet_Ioc fun t ht => ?_
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (inv_nonneg.2 (norm_nonneg _)))
        (norm_nonneg _)
    exact hrem.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C0 0) hν.le) (norm_nonneg _)) htn_nonneg)
  -- 3. Amplitude bound
  have h3 : ‖(S (k + M)).aNuC D.Pl.eigenvalue D.Pl.kappa (D.mu (k + M) z : ℂ) (nu D (k + M)) B‖ ≤
      max Cb 0 * testedNorm (S (k + M)).pk D.Pl.eigenvalue D.Pl.kappa (nu D (k + M))
        (D.mu (k + M) z : ℂ) (1.1 / nu D (k + M)) ((S (k + M)).gB B) := by
    unfold FlatSetting.aNuC
    exact norm_aFrozen_le_testedNorm hν hTfH true
      (fun s hs => (hb (k + M) hn_0 s hs true).2) (by simpa using hf_W)
  exact ⟨h1, h2, h3⟩

end UnforcedLeray.Short.PartIIIb.Concrete.FlatUnif.G3
