import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_3.VBg.Leaves
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.BackgroundSplit.Local
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_2_3.Pt.DilJet
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_3.Formula
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.N0
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.N1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.N2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_1_2.C
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_pres_4_org2_1_2

/-!
# Low-age background jet bound and high-age entrance jet bound (`PartIII-b:C/rep/3/4/1`, helper 2)

Source of record: `the November 2 reference manuscript`, lines 2347-2387,
2516-2520, 5225-5235, 5461-5465.

* On the young range `0 < s ≤ 1`, `vJetDens (L.V τ) y` is split linearly into `rawU` and the two
  inlet columns `p.inlet i = Nv p.R (p.inletProfile i)` (avoiding `coefChgDens`, whose zeroth-order
  term scales as `√s` and is not square-integrable against `s^{-5/2} ds` near `s = 0`).
  - `rawU` has `|DU_raw| = O(s 𝔴₃)` and `|D²U_raw| = O(s^{3/2} 𝔴₃) ≤ O(s 𝔴₃)` from
    `ringChartRules` and `trainMoment`.
  - Each `Nv R b` with `1 ≤ R` and smooth `b` has `vJetDens (Nv R b τ) y ≤ C s (1 + |η|)² Σ_{l≤2} ‖D^l b‖`
    for `0 < s ≤ 1`, proved from `nvPd0`, `nvPd1`, `nvPd2`, `ringFrameD2Formula`, the dilation
    identities in `RingFrameD2BoundAux`, and `dilJetBound`. Combined with `IIb.inletJetDecay` and
    the ball coordinate bound, this gives `O(P_ν s (1 + |η|)⁻¹)`.
* On the late range `1 < s`, `vJetDens (L.V τ) y ≤ vJetDens (rawU D.Pl L τ) y + 12 coefChgDens ...`,
  and `entWPt` bounds `12 coefChgDens ...` by `P_ν (1 + |η|)⁻¹ ≤ P_ν (1 + |η / √s|)⁻¹`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.VBgSq.JetAux

open UnforcedLeray.Blueprint.Planar (PlanarData)
open UnforcedLeray.Cons.C03.Concrete (Params)

theorem vJetDens_nonneg (V : Space → Space) (y : Space) : 0 ≤ vJetDens V y := by
  unfold vJetDens
  exact add_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem vJetDens_eq_grad_add_hess (V : Space → Space) (y : Space) :
    vJetDens V y = gradSize V y + hessSize V y := rfl

theorem vJetDens_sub_le (U W : Space → Space) (y : Space) :
    vJetDens U y ≤ vJetDens W y + 12 * coefChgDens U W y := by
  rw [vJetDens_eq_grad_add_hess, vJetDens_eq_grad_add_hess]
  linarith [gradSize_sub_le U W y, hessSize_sub_le U W y]

/-- Linear triangle inequality for `vJetDens` on `C²` affine combinations `U = W + Σᵢ aᵢ Eᵢ`
on an open set `s` (no zeroth-order `‖Eᵢ y‖` term enters). -/
theorem vJetDens_affine_le (U W : Space → Space) (E : Fin 2 → Space → Space) (a : Fin 2 → ℝ)
    (s : Set Space) (y : Space) (hs : IsOpen s) (hy : y ∈ s)
    (hW : ContDiffOn ℝ 2 W s) (hE : ∀ i, ContDiffOn ℝ 2 (E i) s)
    (hU : ∀ z, U z = W z + ∑ i, a i • E i z) :
    vJetDens U y ≤ vJetDens W y + ∑ i : Fin 2, |a i| * vJetDens (E i) y := by
  have hW1 : ContDiffOn ℝ 1 (fun x => fderiv ℝ W x) s := hW.fderiv_of_isOpen hs (by norm_num)
  have hE1 : ∀ i, ContDiffOn ℝ 1 (fun x => fderiv ℝ (E i) x) s :=
    fun i => (hE i).fderiv_of_isOpen hs (by norm_num)
  have hWd : ∀ x ∈ s, DifferentiableAt ℝ W x :=
    fun x hx => (hW.contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num)
  have hEd : ∀ i, ∀ x ∈ s, DifferentiableAt ℝ (E i) x :=
    fun i x hx => ((hE i).contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num)
  have hWd1 : DifferentiableAt ℝ (fun x => fderiv ℝ W x) y :=
    (hW1.contDiffAt (hs.mem_nhds hy)).differentiableAt (by norm_num)
  have hEd1 : ∀ i, DifferentiableAt ℝ (fun x => fderiv ℝ (E i) x) y :=
    fun i => ((hE1 i).contDiffAt (hs.mem_nhds hy)).differentiableAt (by norm_num)
  have hfd : ∀ x ∈ s, fderiv ℝ U x = fderiv ℝ W x + ∑ i, a i • fderiv ℝ (E i) x := by
    intro x hx
    have hUf : U = fun z => W z + ∑ i, a i • E i z := funext hU
    rw [hUf]
    exact ((hWd x hx).hasFDerivAt.add
      (HasFDerivAt.fun_sum fun i _ => (hEd i x hx).hasFDerivAt.const_smul (a i))).fderiv
  have hev : (fun x => fderiv ℝ U x) =ᶠ[𝓝 y]
      (fun x => fderiv ℝ W x + ∑ i, a i • fderiv ℝ (E i) x) :=
    Filter.eventually_of_mem (hs.mem_nhds hy) hfd
  have hD : HasFDerivAt (fun x => fderiv ℝ W x + ∑ i, a i • fderiv ℝ (E i) x)
      (fderiv ℝ (fun x => fderiv ℝ W x) y +
        ∑ i, a i • fderiv ℝ (fun x => fderiv ℝ (E i) x) y) y :=
    hWd1.hasFDerivAt.add (HasFDerivAt.fun_sum fun i _ => (hEd1 i).hasFDerivAt.const_smul (a i))
  have hdiffU : DifferentiableAt ℝ (fun x => fderiv ℝ U x) y :=
    hD.differentiableAt.congr_of_eventuallyEq hev
  have hsec : secondJet U y = secondJet W y + ∑ i, a i • secondJet (E i) y := by
    rw [secondJet_eq_fderiv hdiffU, hev.fderiv_eq, hD.fderiv, secondJet_eq_fderiv hWd1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [secondJet_eq_fderiv (hEd1 i)]
  have hpd1 : ∀ j : Fin 3, ‖physPd U j y‖ ≤
      ‖physPd W j y‖ + (|a 0| * ‖physPd (E 0) j y‖ + |a 1| * ‖physPd (E 1) j y‖) := by
    intro j
    have heq : physPd U j y = physPd W j y + (a 0 • physPd (E 0) j y + a 1 • physPd (E 1) j y) := by
      unfold physPd
      rw [hfd y hy]
      simp [Fin.sum_univ_two]
    rw [heq]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (norm_add_le _ _).trans ?_
    simp [norm_smul, Real.norm_eq_abs]
  have hpd2 : ∀ j l : Fin 3, ‖physPd2 U j l y‖ ≤
      ‖physPd2 W j l y‖ + (|a 0| * ‖physPd2 (E 0) j l y‖ + |a 1| * ‖physPd2 (E 1) j l y‖) := by
    intro j l
    have heq : physPd2 U j l y =
        physPd2 W j l y + (a 0 • physPd2 (E 0) j l y + a 1 • physPd2 (E 1) j l y) := by
      have hb := congrArg
        (fun M : Space →L[ℝ] Space →L[ℝ] Space => M (coordinateVector j) (coordinateVector l)) hsec
      simpa [Fin.sum_univ_two, secondJet_basis] using hb
    rw [heq]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (norm_add_le _ _).trans ?_
    simp [norm_smul, Real.norm_eq_abs]
  unfold vJetDens
  simp only [Fin.sum_univ_three, Fin.sum_univ_two]
  linarith [hpd1 0, hpd1 1, hpd1 2, hpd2 0 0, hpd2 0 1, hpd2 0 2,
    hpd2 1 0, hpd2 1 1, hpd2 1 2, hpd2 2 0, hpd2 2 1, hpd2 2 2]

/-- Low-age (`0 < s ≤ 1`) bound on `vJetDens (rawU Pl L τ) y`: both `|DU_raw|` and `|D²U_raw|` carry
at least one power of `s` (`s^{3/2} ≤ s` on `(0, 1]`). -/
theorem vJetDens_rawU_early_le (Pl : PlanarData) (L : ReturnLevel) {C1 C2 : ℝ} {k1 k2 : ℕ}
    (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1) (h1 : RingChartRulesAt Pl L C1 k1)
    (h2 : ∀ q : Chart, 0 < q.1 → q.1 ≤ 1 / L.ν → trainWeight 4 L q ≤ C2 * L.ν⁻¹ ^ k2)
    {p : Chart} (hp : 0 < p.1) (hp1 : p.1 ≤ 1) :
    vJetDens (rawU Pl L (NearInst.chartTau L.ε⁻¹ p)) (NearInst.chartY L.ε⁻¹ p) ≤
      12 * (2 + |C1|) * max C2 0 * L.ν⁻¹ ^ (k1 + k2) * p.1 * (1 + |p.2.2|)⁻¹ := by
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hνinv1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hp_nu : p.1 ≤ 1 / L.ν := by
    rw [one_div]
    exact hp1.trans hνinv1
  set τ := NearInst.chartTau L.ε⁻¹ p
  set y := NearInst.chartY L.ε⁻¹ p
  set W := trainWeight 3 L p
  set P1 := L.ν⁻¹ ^ k1
  set A1 := (2 + |C1|) * P1
  have hW0 : 0 ≤ W := trainWeight_nonneg 3 L p
  have hP1 : 1 ≤ P1 := one_le_pow₀ hνinv1
  have hA10 : 0 ≤ A1 := by positivity
  have hs0 : 0 ≤ p.1 := hp.le
  have hs32_0 : 0 ≤ p.1 ^ (3 / 2 : ℝ) := Real.rpow_nonneg hs0 _
  have hs32_le : p.1 ^ (3 / 2 : ℝ) ≤ p.1 := by
    calc p.1 ^ (3 / 2 : ℝ) ≤ p.1 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hp hp1 (by norm_num)
      _ = p.1 := Real.rpow_one p.1
  have hPd : ∀ j : Fin 3, ‖physPd (rawU Pl L τ) j y‖ ≤ A1 * p.1 * W := fun j =>
    bound_of_close _ (vecSp (flatD1 L p.1 p.2 j)) p.1 W C1 P1 L.ε hs0 hW0 hP1 hε.le hε1
      ((norm_vecSp_le _).trans (mul_le_mul_of_nonneg_left (trainFlatD1Bound L p hp j)
        (by norm_num))) ((h1 p hp hp_nu).2.1 j)
  have hPd2 : ∀ j l : Fin 3, ‖physPd2 (rawU Pl L τ) j l y‖ ≤ A1 * p.1 * W := fun j l => by
    have h := bound_of_close _ (vecSp (flatD2 L p.1 p.2 j l)) (p.1 ^ (3 / 2 : ℝ)) W C1 P1 L.ε
      hs32_0 hW0 hP1 hε.le hε1
      ((norm_vecSp_le _).trans (mul_le_mul_of_nonneg_left (trainFlatD2Bound L p hp j l)
        (by norm_num))) ((h1 p hp hp_nu).2.2.1 j l)
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs32_le hA10) hW0)
  have h4 : trainWeight 4 L p ≤ max C2 0 * L.ν⁻¹ ^ k2 :=
    (h2 p hp hp_nu).trans (mul_le_mul_of_nonneg_right (le_max_left C2 0) (by positivity))
  have hW_eta : W ≤ max C2 0 * L.ν⁻¹ ^ k2 * (1 + |p.2.2|)⁻¹ :=
    trainWeight_three_le_inv_eta L h4
  have hsum : vJetDens (rawU Pl L τ) y ≤ 12 * (A1 * p.1 * W) := by
    unfold vJetDens
    simp only [Fin.sum_univ_three]
    linarith [hPd 0, hPd 1, hPd 2, hPd2 0 0, hPd2 0 1, hPd2 0 2,
      hPd2 1 0, hPd2 1 1, hPd2 1 2, hPd2 2 0, hPd2 2 1, hPd2 2 2]
  calc vJetDens (rawU Pl L τ) y
      ≤ 12 * A1 * p.1 * W := by linarith
    _ ≤ 12 * A1 * p.1 * (max C2 0 * L.ν⁻¹ ^ k2 * (1 + |p.2.2|)⁻¹) :=
        mul_le_mul_of_nonneg_left hW_eta (by positivity)
    _ = 12 * (2 + |C1|) * max C2 0 * L.ν⁻¹ ^ (k1 + k2) * p.1 * (1 + |p.2.2|)⁻¹ := by
        simp only [A1, P1, pow_add]; ring

section NvEarly

open RingFrameD2BoundAux
open RingFrameD2FormulaAux (contDiffAt_Drho contDiffAt_Dz)
open RingChartRawD2Sub (Nv_eq_frame_bSqrt ringFrameD2_00 ringFrameD2_01 ringFrameD2_02
  ringFrameD2_10 ringFrameD2_11 ringFrameD2_12 ringFrameD2_20 ringFrameD2_21 ringFrameD2_22)

private lemma dil_J2_le (b : Chart → Merid)
    (hb : ContDiffOn ℝ ∞ b (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    {pt : Chart} (hp0 : 0 < pt.1) (hp1 : pt.1 ≤ 1) :
    J 2 (fun z' : Zc => b (phi z')) (Real.log pt.1, pt.2) ≤
      11 * ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l b pt‖ := by
  set bHat : Zc → Merid := fun z' => b (phi z')
  set z : Zc := (Real.log pt.1, pt.2)
  set S : ℝ := ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l b pt‖
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hd0 : ‖iteratedFDeriv ℝ 0 bHat z‖ ≤
      ((0 : ℕ).factorial : ℝ) * (∑ i ∈ Finset.range 1, ‖iteratedFDeriv ℝ i b pt‖) *
        (1 + pt.1) ^ 0 := dilJetBound Merid b hb 0 pt.1 hp0 pt.2
  have hd1 : ‖iteratedFDeriv ℝ 1 bHat z‖ ≤
      ((1 : ℕ).factorial : ℝ) * (∑ i ∈ Finset.range 2, ‖iteratedFDeriv ℝ i b pt‖) *
        (1 + pt.1) ^ 1 := dilJetBound Merid b hb 1 pt.1 hp0 pt.2
  have hd2 : ‖iteratedFDeriv ℝ 2 bHat z‖ ≤
      ((2 : ℕ).factorial : ℝ) * S * (1 + pt.1) ^ 2 := dilJetBound Merid b hb 2 pt.1 hp0 pt.2
  have hf0 : ((0 : ℕ).factorial : ℝ) = 1 := by norm_num [Nat.factorial]
  have hf1 : ((1 : ℕ).factorial : ℝ) = 1 := by norm_num [Nat.factorial]
  have hf2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hf0, pow_zero, one_mul, mul_one] at hd0
  rw [hf1, pow_one, one_mul] at hd1
  rw [hf2] at hd2
  have hsub0 : ∑ i ∈ Finset.range 1, ‖iteratedFDeriv ℝ i b pt‖ ≤ S :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by norm_num))
      fun _ _ _ => norm_nonneg _
  have hsub1 : ∑ i ∈ Finset.range 2, ‖iteratedFDeriv ℝ i b pt‖ ≤ S :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by norm_num))
      fun _ _ _ => norm_nonneg _
  have hp_1 : 1 + pt.1 ≤ 2 := by linarith
  have hp_2 : (1 + pt.1) ^ 2 ≤ 4 := by
    calc (1 + pt.1) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (by linarith) hp_1 2
      _ = 4 := by norm_num
  have hb0 : ‖iteratedFDeriv ℝ 0 bHat z‖ ≤ S := hd0.trans hsub0
  have hb1 : ‖iteratedFDeriv ℝ 1 bHat z‖ ≤ 2 * S := by
    calc ‖iteratedFDeriv ℝ 1 bHat z‖
        ≤ (∑ i ∈ Finset.range 2, ‖iteratedFDeriv ℝ i b pt‖) * (1 + pt.1) := hd1
      _ ≤ S * 2 := mul_le_mul hsub1 hp_1 (by linarith) hS0
      _ = 2 * S := by ring
  have hb2 : ‖iteratedFDeriv ℝ 2 bHat z‖ ≤ 8 * S := by
    calc ‖iteratedFDeriv ℝ 2 bHat z‖
        ≤ 2 * S * (1 + pt.1) ^ 2 := hd2
      _ ≤ 2 * S * 4 := mul_le_mul_of_nonneg_left hp_2 (mul_nonneg zero_le_two hS0)
      _ = 8 * S := by ring
  unfold J
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  linarith

private lemma ringFrameD2_sum_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (b : Chart → Merid)
    (hb : ContDiffOn ℝ ∞ b (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))) (z : Zc) :
    ∑ j : Fin 3, ∑ l : Fin 3, ‖ringFrameD2 ε (bSqrt b) (phi z) j l‖ ≤
      94 * wt (3 / 2) z * (1 + |z.2.2|) ^ 2 * J 2 (fun z' => b (phi z')) z := by
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hbSq2 : ContDiffOn ℝ 2 (bSqrt b) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    intro x hx
    have hsq : ContDiffAt ℝ 2 (fun w : ℝ × (ℝ × ℝ) => Real.sqrt w.1) x :=
      (Real.contDiffAt_sqrt hx.1.ne').comp x contDiff_fst.contDiffAt
    have hbx : ContDiffAt ℝ 2 b x := (hb.contDiffAt (hopen.mem_nhds hx)).of_le (by simp)
    exact (hsq.smul hbx).contDiffWithinAt
  set bHat : Zc → Merid := fun z' => b (phi z')
  have hphi_smooth : ContDiff ℝ ∞ phi :=
    (Real.contDiff_exp.comp contDiff_fst).prodMk contDiff_snd
  have hbHat : ContDiff ℝ ∞ bHat :=
    hb.comp_contDiff hphi_smooth fun z' => ⟨Real.exp_pos _, mem_univ _⟩
  have hlift_B : ∀ z' : Zc, bSqrt b (phi z') = wt (1 / 2) z' • bHat z' := by
    intro z'
    unfold bSqrt wt phi bHat
    rw [exp_half_eq]
    rfl
  have hlift_B_fun : (fun z' => bSqrt b (phi z')) = fun z' => wt (1 / 2) z' • bHat z' :=
    funext hlift_B
  have hcd_B : ∀ z' : Zc, ContDiffAt ℝ 2 (bSqrt b) (phi z') := fun z' =>
    hbSq2.contDiffAt (hopen.mem_nhds ⟨Real.exp_pos _, mem_univ _⟩)
  have hdiff_B : ∀ z' : Zc, DifferentiableAt ℝ (bSqrt b) (phi z') := fun z' =>
    (hcd_B z').differentiableAt (by norm_num)
  have hdiff_Drho : ∀ z' : Zc, DifferentiableAt ℝ (Drho ε (bSqrt b)) (phi z') := fun z' =>
    (contDiffAt_Drho ε (Real.exp_pos _) (hcd_B z')).differentiableAt (by norm_num)
  have hdiff_Dz : ∀ z' : Zc, DifferentiableAt ℝ (Dz (bSqrt b)) (phi z') := fun z' =>
    (contDiffAt_Dz (Real.exp_pos _) (hcd_B z')).differentiableAt (by norm_num)
  have hDrho_B : ∀ z' : Zc, Drho ε (bSqrt b) (phi z') = wt 1 z' • Pm ε 1 bHat z' := by
    intro z'
    rw [lift_Drho _ (hdiff_B z'), hlift_B_fun, Pm_wt _ _ _ hbHat]
    simp only [smul_smul, wt_mul]
    norm_num
  have hDz_B : ∀ z' : Zc, Dz (bSqrt b) (phi z') = wt 1 z' • Zo bHat z' := by
    intro z'
    rw [lift_Dz (hdiff_B z'), hlift_B_fun, Zo_wt _ hbHat]
    simp only [smul_smul, wt_mul]
    norm_num
  set we : ℝ := 1 + |z.2.2|
  have hwe1 : 1 ≤ we := by simp only [we]; linarith [abs_nonneg z.2.2]
  have hwe0 : 0 ≤ we := by linarith
  have hwe_sq : we ≤ we ^ 2 := by rw [sq]; exact le_mul_of_one_le_left hwe0 hwe1
  have hwe2_1 : 1 ≤ we ^ 2 := one_le_pow₀ hwe1
  have hwt0 : 0 ≤ wt (3 / 2) z := (wt_pos _ _).le
  set J2 : ℝ := J 2 bHat z
  have hJ2_0 : 0 ≤ J2 := J_nonneg 2 bHat z
  have hP1 : ‖Pm ε 1 bHat z‖ ≤ 7 * we * J2 := by
    calc ‖Pm ε 1 bHat z‖ ≤ J 0 (Pm ε 1 bHat) z := norm_le_J 0 (Pm ε 1 bHat) z
      _ ≤ 7 * we * J 1 bHat z :=
          J_Pm hε0 hε1 (m := 1) (by norm_num) (n := 0) (by norm_num) hbHat z
      _ ≤ 7 * we * J2 :=
          mul_le_mul_of_nonneg_left (J_mono (show 1 ≤ 2 by norm_num) bHat z) (by positivity)
  have hP2 : ‖Pm ε 2 bHat z‖ ≤ 7 * we * J2 := by
    calc ‖Pm ε 2 bHat z‖ ≤ J 0 (Pm ε 2 bHat) z := norm_le_J 0 (Pm ε 2 bHat) z
      _ ≤ 7 * we * J 1 bHat z :=
          J_Pm hε0 hε1 (m := 2) (by norm_num) (n := 0) (by norm_num) hbHat z
      _ ≤ 7 * we * J2 :=
          mul_le_mul_of_nonneg_left (J_mono (show 1 ≤ 2 by norm_num) bHat z) (by positivity)
  have hZo : ‖Zo bHat z‖ ≤ J2 := by
    calc ‖Zo bHat z‖ ≤ J 0 (Zo bHat) z := norm_le_J 0 (Zo bHat) z
      _ ≤ J 1 bHat z := J_Zo (n := 0) hbHat z
      _ ≤ J2 := J_mono (show 1 ≤ 2 by norm_num) bHat z
  have hs_phi : Real.sqrt (phi z).1 = wt (1 / 2) z := (wt_half z).symm
  have h1_phi : (phi z).1 = wt 1 z := (wt_one z).symm
  have hhA : ε * Real.sqrt (phi z).1 * (Drho ε (bSqrt b) (phi z)) 0 -
      ε ^ 2 * (phi z).1 * (bSqrt b (phi z)) 0 = ε * wt (3 / 2) z * (Pm ε 2 bHat z) 0 := by
    rw [hs_phi, h1_phi, hDrho_B z, hlift_B z, Pm_step, wt_split]
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    ring
  have hhC : ε * Real.sqrt (phi z).1 * (Drho ε (bSqrt b) (phi z)) 1 =
      ε * wt (3 / 2) z * (Pm ε 1 bHat z) 1 := by
    rw [hs_phi, hDrho_B z, wt_split]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hhZ : ε * Real.sqrt (phi z).1 * (Dz (bSqrt b) (phi z)) 0 =
      ε * wt (3 / 2) z * (Zo bHat z) 0 := by
    rw [hs_phi, hDz_B z, wt_split]
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  have hεwt : ε * wt (3 / 2) z ≤ wt (3 / 2) z := by
    calc ε * wt (3 / 2) z ≤ 1 * wt (3 / 2) z := mul_le_mul_of_nonneg_right hε1 hwt0
      _ = wt (3 / 2) z := one_mul _
  have habsA : |ε * wt (3 / 2) z * (Pm ε 2 bHat z) 0| ≤ 7 * wt (3 / 2) z * we ^ 2 * J2 := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hε0 hwt0)]
    have h1 : |(Pm ε 2 bHat z) 0| ≤ 7 * we * J2 := (comp_le _ 0).trans hP2
    calc ε * wt (3 / 2) z * |(Pm ε 2 bHat z) 0|
        ≤ wt (3 / 2) z * (7 * we * J2) := mul_le_mul hεwt h1 (abs_nonneg _) hwt0
      _ = 7 * wt (3 / 2) z * J2 * we := by ring
      _ ≤ 7 * wt (3 / 2) z * J2 * we ^ 2 := mul_le_mul_of_nonneg_left hwe_sq (by positivity)
      _ = 7 * wt (3 / 2) z * we ^ 2 * J2 := by ring
  have habsC : |ε * wt (3 / 2) z * (Pm ε 1 bHat z) 1| ≤ 7 * wt (3 / 2) z * we ^ 2 * J2 := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hε0 hwt0)]
    have h1 : |(Pm ε 1 bHat z) 1| ≤ 7 * we * J2 := (comp_le _ 1).trans hP1
    calc ε * wt (3 / 2) z * |(Pm ε 1 bHat z) 1|
        ≤ wt (3 / 2) z * (7 * we * J2) := mul_le_mul hεwt h1 (abs_nonneg _) hwt0
      _ = 7 * wt (3 / 2) z * J2 * we := by ring
      _ ≤ 7 * wt (3 / 2) z * J2 * we ^ 2 := mul_le_mul_of_nonneg_left hwe_sq (by positivity)
      _ = 7 * wt (3 / 2) z * we ^ 2 * J2 := by ring
  have habsZ : |ε * wt (3 / 2) z * (Zo bHat z) 0| ≤ wt (3 / 2) z * we ^ 2 * J2 := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hε0 hwt0)]
    have h1 : |(Zo bHat z) 0| ≤ J2 := (comp_le _ 0).trans hZo
    calc ε * wt (3 / 2) z * |(Zo bHat z) 0|
        ≤ wt (3 / 2) z * J2 := mul_le_mul hεwt h1 (abs_nonneg _) hwt0
      _ = wt (3 / 2) z * J2 * 1 := by ring
      _ ≤ wt (3 / 2) z * J2 * we ^ 2 :=
          mul_le_mul_of_nonneg_left hwe2_1 (mul_nonneg hwt0 hJ2_0)
      _ = wt (3 / 2) z * we ^ 2 * J2 := by ring
  have he00 : ‖ringFrameD2 ε (bSqrt b) (phi z) 0 0‖ ≤ 49 * wt (3 / 2) z * we ^ 2 * J2 := by
    rw [ringFrameD2_00, lift_Drho _ (hdiff_Drho z), funext hDrho_B,
      Pm_wt _ _ _ (contDiff_Pm _ _ hbHat)]
    simp only [smul_smul, wt_mul, show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num,
      show (0 : ℝ) + 2 * 1 = 2 by norm_num, norm_merSp, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hwt0]
    calc wt (3 / 2) z * ‖Pm ε 2 (Pm ε 1 bHat) z‖
        ≤ wt (3 / 2) z * (49 * we ^ 2 * J2) :=
          mul_le_mul_of_nonneg_left (s_P2P1 hε0 hε1 hbHat z) hwt0
      _ = 49 * wt (3 / 2) z * we ^ 2 * J2 := by ring
  have he02 : ‖ringFrameD2 ε (bSqrt b) (phi z) 0 2‖ ≤ 7 * wt (3 / 2) z * we ^ 2 * J2 := by
    rw [ringFrameD2_02, lift_Drho _ (hdiff_Dz z), funext hDz_B, Pm_wt _ _ _ (contDiff_Zo hbHat)]
    simp only [smul_smul, wt_mul, show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num,
      show (0 : ℝ) + 2 * 1 = 2 by norm_num, norm_merSp, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hwt0]
    calc wt (3 / 2) z * ‖Pm ε 2 (Zo bHat) z‖
        ≤ wt (3 / 2) z * (7 * we * J2) :=
          mul_le_mul_of_nonneg_left (s_P2Zo hε0 hε1 hbHat z) hwt0
      _ = 7 * wt (3 / 2) z * J2 * we := by ring
      _ ≤ 7 * wt (3 / 2) z * J2 * we ^ 2 := mul_le_mul_of_nonneg_left hwe_sq (by positivity)
      _ = 7 * wt (3 / 2) z * we ^ 2 * J2 := by ring
  have he20 : ‖ringFrameD2 ε (bSqrt b) (phi z) 2 0‖ ≤ 7 * wt (3 / 2) z * we ^ 2 * J2 := by
    rw [ringFrameD2_20, lift_Dz (hdiff_Drho z), funext hDrho_B, Zo_wt _ (contDiff_Pm _ _ hbHat)]
    simp only [smul_smul, wt_mul, show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num, norm_merSp, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hwt0]
    calc wt (3 / 2) z * ‖Zo (Pm ε 1 bHat) z‖
        ≤ wt (3 / 2) z * (7 * we * J2) :=
          mul_le_mul_of_nonneg_left (s_ZoP1 hε0 hε1 hbHat z) hwt0
      _ = 7 * wt (3 / 2) z * J2 * we := by ring
      _ ≤ 7 * wt (3 / 2) z * J2 * we ^ 2 := mul_le_mul_of_nonneg_left hwe_sq (by positivity)
      _ = 7 * wt (3 / 2) z * we ^ 2 * J2 := by ring
  have he22 : ‖ringFrameD2 ε (bSqrt b) (phi z) 2 2‖ ≤ wt (3 / 2) z * we ^ 2 * J2 := by
    rw [ringFrameD2_22, lift_Dz (hdiff_Dz z), funext hDz_B, Zo_wt _ (contDiff_Zo hbHat)]
    simp only [smul_smul, wt_mul, show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num, norm_merSp, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hwt0]
    calc wt (3 / 2) z * ‖Zo (Zo bHat) z‖
        ≤ wt (3 / 2) z * J2 := mul_le_mul_of_nonneg_left (s_ZoZo hbHat z) hwt0
      _ = wt (3 / 2) z * J2 * 1 := by ring
      _ ≤ wt (3 / 2) z * J2 * we ^ 2 :=
          mul_le_mul_of_nonneg_left hwe2_1 (mul_nonneg hwt0 hJ2_0)
      _ = wt (3 / 2) z * we ^ 2 * J2 := by ring
  have he01 : ‖ringFrameD2 ε (bSqrt b) (phi z) 0 1‖ ≤ 7 * wt (3 / 2) z * we ^ 2 * J2 := by
    rw [ringFrameD2_01, hhA, norm_vecSp_mid]; exact habsA
  have he10 : ‖ringFrameD2 ε (bSqrt b) (phi z) 1 0‖ ≤ 7 * wt (3 / 2) z * we ^ 2 * J2 := by
    rw [ringFrameD2_10, hhA, norm_vecSp_mid]; exact habsA
  have he11 : ‖ringFrameD2 ε (bSqrt b) (phi z) 1 1‖ ≤ 14 * wt (3 / 2) z * we ^ 2 * J2 := by
    rw [ringFrameD2_11, hhA, hhC]
    exact (RingFrameD2BoundAux.norm_vecSp_le _ _).trans (by linarith)
  have he12 : ‖ringFrameD2 ε (bSqrt b) (phi z) 1 2‖ ≤ wt (3 / 2) z * we ^ 2 * J2 := by
    rw [ringFrameD2_12, hhZ, norm_vecSp_mid]; exact habsZ
  have he21 : ‖ringFrameD2 ε (bSqrt b) (phi z) 2 1‖ ≤ wt (3 / 2) z * we ^ 2 * J2 := by
    rw [ringFrameD2_21, hhZ, norm_vecSp_mid]; exact habsZ
  simp only [Fin.sum_univ_three]
  linarith

/-- Universal low-age (`0 < s ≤ 1`) bound on `vJetDens (Nv R b τ) y` for `1 ≤ R` and smooth `b`. -/
theorem vJetDens_Nv_early_le {R : ℝ} (hR : 1 ≤ R) (b : Chart → Merid)
    (hb : ContDiffOn ℝ ∞ b (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))))
    {pt : Chart} (hp0 : 0 < pt.1) (hp1 : pt.1 ≤ 1) :
    vJetDens (Nv R b (NearInst.chartTau R pt)) (NearInst.chartY R pt) ≤
      1100 * pt.1 * (1 + |pt.2.2|) ^ 2 *
        ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l b pt‖ := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  set ε : ℝ := R⁻¹
  have hε0 : 0 ≤ ε := inv_nonneg.2 hR0.le
  have hε1 : ε ≤ 1 := inv_le_one_of_one_le₀ hR
  set τ := NearInst.chartTau R pt
  set y := NearInst.chartY R pt
  have hy0 : 0 < y 0 := by
    simp only [y, NearInst.chartY]
    exact div_pos hR0 (Real.sqrt_pos.2 hp0)
  have hy1 : y 1 = 0 := by simp [y, NearInst.chartY]
  have hch : chart R τ y = pt := chartId R pt hR0 hp0
  have hage : UnforcedLeray.Axi.age R y = pt.1 := congrArg Prod.fst hch
  have htr : UnforcedLeray.Axi.trans R y = pt.2.2 := congrArg (fun x => x.2.2) hch
  have hopen : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := isOpen_Ioi.prod isOpen_univ
  have hpt_mem : pt ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) := ⟨hp0, mem_univ _⟩
  have hb_diff : DifferentiableAt ℝ b (chart R τ y) := by
    rw [hch]
    exact (hb.contDiffAt (hopen.mem_nhds hpt_mem)).differentiableAt (by simp)
  set S : ℝ := ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l b pt‖
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hb0_le : ‖b pt‖ ≤ S := by
    have h := Finset.single_le_sum (f := fun l => ‖iteratedFDeriv ℝ l b pt‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by norm_num : 0 < 3))
    simpa [norm_iteratedFDeriv_zero] using h
  have hb1_le : ‖fderiv ℝ b pt‖ ≤ S := by
    have h := Finset.single_le_sum (f := fun l => ‖iteratedFDeriv ℝ l b pt‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by norm_num : 1 < 3))
    simpa [norm_iteratedFDeriv_one] using h
  have hdQ : ‖UnforcedLeray.Axi.dQ b pt‖ ≤ S := by
    have h := (fderiv ℝ b pt).le_opNorm ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))
    rw [norm_dir_one 0 1 0 (by simp), mul_one] at h
    exact h.trans hb1_le
  have hdS : ‖UnforcedLeray.Axi.dS b pt‖ ≤ S := by
    have h := (fderiv ℝ b pt).le_opNorm ((1 : ℝ), ((0 : ℝ), (0 : ℝ)))
    rw [norm_dir_one 1 0 0 (by simp), mul_one] at h
    exact h.trans hb1_le
  have hdEta : ‖UnforcedLeray.Axi.dEta b pt‖ ≤ S := by
    have h := (fderiv ℝ b pt).le_opNorm ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))
    rw [norm_dir_one 0 0 1 (by simp), mul_one] at h
    exact h.trans hb1_le
  set we : ℝ := 1 + |pt.2.2|
  have hwe1 : 1 ≤ we := by simp only [we]; linarith [abs_nonneg pt.2.2]
  have hwe0 : 0 ≤ we := by linarith
  have hwe2 : 1 ≤ we ^ 2 := one_le_pow₀ hwe1
  have hpd0 : ‖physPd (Nv R b τ) 0 y‖ ≤ 4 * pt.1 * we ^ 2 * S := by
    rw [nvPd0 R τ b y hR0 hy0 hy1 hb_diff, hch, hage, htr, norm_smul, norm_merSp,
      Real.norm_eq_abs, abs_of_pos hp0]
    have hsub : ‖UnforcedLeray.Axi.dQ b pt - ε • (b pt + (2 * pt.1) • UnforcedLeray.Axi.dS b pt +
        pt.2.2 • UnforcedLeray.Axi.dEta b pt)‖ ≤ 4 * we ^ 2 * S := by
      have h1 := norm_sub_le (UnforcedLeray.Axi.dQ b pt)
        (ε • (b pt + (2 * pt.1) • UnforcedLeray.Axi.dS b pt +
          pt.2.2 • UnforcedLeray.Axi.dEta b pt))
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε0] at h1
      have h2 := norm_add_le (b pt + (2 * pt.1) • UnforcedLeray.Axi.dS b pt)
        (pt.2.2 • UnforcedLeray.Axi.dEta b pt)
      have h3 := norm_add_le (b pt) ((2 * pt.1) • UnforcedLeray.Axi.dS b pt)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * pt.1)] at h3
      rw [norm_smul, Real.norm_eq_abs] at h2
      have hm1 : 2 * pt.1 * ‖UnforcedLeray.Axi.dS b pt‖ ≤ 2 * S := by
        calc 2 * pt.1 * ‖UnforcedLeray.Axi.dS b pt‖
            ≤ 2 * 1 * S :=
              mul_le_mul (mul_le_mul_of_nonneg_left hp1 zero_le_two) hdS (norm_nonneg _)
                (by norm_num)
          _ = 2 * S := by ring
      have hm2 : |pt.2.2| * ‖UnforcedLeray.Axi.dEta b pt‖ ≤ |pt.2.2| * S :=
        mul_le_mul_of_nonneg_left hdEta (abs_nonneg _)
      have hmid : ‖b pt + (2 * pt.1) • UnforcedLeray.Axi.dS b pt +
          pt.2.2 • UnforcedLeray.Axi.dEta b pt‖ ≤ (3 + |pt.2.2|) * S := by
        linarith
      have hεm : ε * ‖b pt + (2 * pt.1) • UnforcedLeray.Axi.dS b pt +
          pt.2.2 • UnforcedLeray.Axi.dEta b pt‖ ≤ (3 + |pt.2.2|) * S := by
        calc ε * _ ≤ 1 * ((3 + |pt.2.2|) * S) :=
              mul_le_mul hε1 hmid (norm_nonneg _) zero_le_one
          _ = (3 + |pt.2.2|) * S := one_mul _
      have hwe4 : (4 + |pt.2.2|) * S ≤ 4 * we ^ 2 * S := by
        refine mul_le_mul_of_nonneg_right ?_ hS0
        have hsq : 0 ≤ |pt.2.2| ^ 2 := sq_nonneg _
        have habs : 0 ≤ |pt.2.2| := abs_nonneg _
        have hid : 4 * we ^ 2 - (4 + |pt.2.2|) = 7 * |pt.2.2| + 4 * |pt.2.2| ^ 2 := by
          simp only [we]; ring
        linarith
      linarith
    calc pt.1 * _ ≤ pt.1 * (4 * we ^ 2 * S) := mul_le_mul_of_nonneg_left hsub hp0.le
      _ = 4 * pt.1 * we ^ 2 * S := by ring
  have hpd1 : ‖physPd (Nv R b τ) 1 y‖ ≤ pt.1 * we ^ 2 * S := by
    rw [nvPd1 R τ b y hR0 hy0 hy1 hb_diff, hch, hage, norm_vecSp_mid, abs_mul, abs_mul,
      abs_of_nonneg hε0, abs_of_pos hp0]
    have hb00 : |b pt 0| ≤ S := (comp_le (b pt) 0).trans hb0_le
    calc ε * pt.1 * |b pt 0|
        ≤ 1 * pt.1 * S :=
          mul_le_mul (mul_le_mul_of_nonneg_right hε1 hp0.le) hb00 (abs_nonneg _) (by positivity)
      _ = pt.1 * S * 1 := by ring
      _ ≤ pt.1 * S * we ^ 2 := mul_le_mul_of_nonneg_left hwe2 (mul_nonneg hp0.le hS0)
      _ = pt.1 * we ^ 2 * S := by ring
  have hpd2_1 : ‖physPd (Nv R b τ) 2 y‖ ≤ pt.1 * we ^ 2 * S := by
    rw [nvPd2 R τ b y hR0 hy0 hy1 hb_diff, hch, hage, norm_smul, norm_merSp, Real.norm_eq_abs,
      abs_of_pos hp0]
    calc pt.1 * ‖UnforcedLeray.Axi.dEta b pt‖
        ≤ pt.1 * S := mul_le_mul_of_nonneg_left hdEta hp0.le
      _ = pt.1 * S * 1 := by ring
      _ ≤ pt.1 * S * we ^ 2 := mul_le_mul_of_nonneg_left hwe2 (mul_nonneg hp0.le hS0)
      _ = pt.1 * we ^ 2 * S := by ring
  have hbSq2 : ContDiffOn ℝ 2 (bSqrt b) (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) := by
    intro x hx
    have hsq : ContDiffAt ℝ 2 (fun w : ℝ × (ℝ × ℝ) => Real.sqrt w.1) x :=
      (Real.contDiffAt_sqrt hx.1.ne').comp x contDiff_fst.contDiffAt
    have hbx : ContDiffAt ℝ 2 b x := (hb.contDiffAt (hopen.mem_nhds hx)).of_le (by simp)
    exact (hsq.smul hbx).contDiffWithinAt
  set z : Zc := (Real.log pt.1, pt.2)
  have hphi_z : phi z = pt := phi_log hp0
  have hwt32 : wt (3 / 2) z = pt.1 ^ (3 / 2 : ℝ) := by
    rw [wt_three_half]
    simp [z, Real.exp_log hp0]
  have hs32_le : wt (3 / 2) z ≤ pt.1 := by
    rw [hwt32]
    calc pt.1 ^ (3 / 2 : ℝ) ≤ pt.1 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hp0 hp1 (by norm_num)
      _ = pt.1 := Real.rpow_one pt.1
  set J2 : ℝ := J 2 (fun z' => b (phi z')) z
  have hJ2_0 : 0 ≤ J2 := J_nonneg 2 _ z
  have hJ2_le : J2 ≤ 11 * S := dil_J2_le b hb hp0 hp1
  have hpd2_eq : ∀ j l : Fin 3,
      physPd2 (Nv R b τ) j l y = ringFrameD2 ε (bSqrt b) (phi z) j l := by
    intro j l
    rw [Nv_eq_frame_bSqrt, ringFrameD2Formula R τ (bSqrt b) y hR0 hy0 hy1 hbSq2 j l, hch, hphi_z]
  have hsum2_S : ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 (Nv R b τ) j l y‖ ≤
      1034 * pt.1 * we ^ 2 * S := by
    have hr := ringFrameD2_sum_le hε0 hε1 b hb z
    have heq_sum : ∑ j : Fin 3, ∑ l : Fin 3, ‖physPd2 (Nv R b τ) j l y‖ =
        ∑ j : Fin 3, ∑ l : Fin 3, ‖ringFrameD2 ε (bSqrt b) (phi z) j l‖ := by
      simp only [hpd2_eq]
    rw [heq_sum]
    calc ∑ j : Fin 3, ∑ l : Fin 3, ‖ringFrameD2 ε (bSqrt b) (phi z) j l‖
        ≤ 94 * wt (3 / 2) z * we ^ 2 * J2 := hr
      _ = 94 * we ^ 2 * J2 * wt (3 / 2) z := by ring
      _ ≤ 94 * we ^ 2 * J2 * pt.1 :=
          mul_le_mul_of_nonneg_left hs32_le (by positivity)
      _ = 94 * pt.1 * we ^ 2 * J2 := by ring
      _ ≤ 94 * pt.1 * we ^ 2 * (11 * S) :=
          mul_le_mul_of_nonneg_left hJ2_le (by positivity)
      _ = 1034 * pt.1 * we ^ 2 * S := by ring
  unfold vJetDens
  have hsum1 : ∑ j : Fin 3, ‖physPd (Nv R b τ) j y‖ ≤ 6 * pt.1 * we ^ 2 * S := by
    rw [Fin.sum_univ_three]
    linarith
  have h0 : 0 ≤ pt.1 * we ^ 2 * S := by positivity
  linarith

end NvEarly

/-- Exponential absorption `(1 + t)² e^{-(κ ν²) t} ≤ (min 1 (κ / 3))⁻³ ν⁻⁶ (1 + t)⁻¹`
for `κ > 0`, `0 < ν ≤ 1`, and `t ≥ 0`. -/
theorem sq_exp_neg_le_inv_one_add {κ ν t : ℝ} (hκ : 0 < κ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (ht : 0 ≤ t) :
    (1 + t) ^ 2 * Real.exp (-(κ * ν ^ 2) * t) ≤
      (min 1 (κ / 3))⁻¹ ^ 3 * ν⁻¹ ^ 6 * (1 + t)⁻¹ := by
  set m := min 1 (κ / 3)
  have hm0 : 0 < m := lt_min one_pos (by positivity)
  set δ := m * ν ^ 2
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    calc δ ≤ 1 * 1 ^ 2 :=
          mul_le_mul (min_le_left 1 (κ / 3)) (pow_le_pow_left₀ hν.le hν1 2) (by positivity)
            zero_le_one
      _ = 1 := by ring
  have hδk : δ ≤ κ / 3 * ν ^ 2 := mul_le_mul_of_nonneg_right (min_le_right 1 (κ / 3)) (sq_nonneg ν)
  have h1 : δ * (1 + t) ≤ Real.exp (κ / 3 * ν ^ 2 * t) := by
    have ha : δ * (1 + t) ≤ 1 + κ / 3 * ν ^ 2 * t := by nlinarith
    exact ha.trans (by linarith [Real.add_one_le_exp (κ / 3 * ν ^ 2 * t)])
  have h3 : (δ * (1 + t)) ^ 3 ≤ Real.exp (κ * ν ^ 2 * t) := by
    calc (δ * (1 + t)) ^ 3 ≤ Real.exp (κ / 3 * ν ^ 2 * t) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h1 3
      _ = Real.exp ((3 : ℕ) * (κ / 3 * ν ^ 2 * t)) := (Real.exp_nat_mul _ 3).symm
      _ = Real.exp (κ * ν ^ 2 * t) := by congr 1; push_cast; ring
  have hexp : Real.exp (-(κ * ν ^ 2) * t) ≤ ((δ * (1 + t)) ^ 3)⁻¹ := by
    rw [show -(κ * ν ^ 2) * t = -(κ * ν ^ 2 * t) by ring, Real.exp_neg]
    exact inv_anti₀ (by positivity) h3
  have ht1 : 0 < 1 + t := by linarith
  calc (1 + t) ^ 2 * Real.exp (-(κ * ν ^ 2) * t)
      ≤ (1 + t) ^ 2 * ((δ * (1 + t)) ^ 3)⁻¹ :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = m⁻¹ ^ 3 * ν⁻¹ ^ 6 * (1 + t)⁻¹ := by
        simp only [δ]
        field_simp

/-- Ball coordinate bound `|p.coord z i| ≤ C₀ (p.ν ^ k₀)⁻¹ e^{m₀ / p.ν} p.ε`. -/
theorem coord_le_rhoB (p : Params) (m0 C0 : ℝ) (k0 : ℕ) (z : p.Z)
    (hz : ‖z‖ ≤ UnforcedLeray.Short.IIb.rhoB p m0 C0 k0) (i : Fin 2) :
    |p.coord z i| ≤ C0 * (p.ν ^ k0)⁻¹ * Real.exp (m0 / p.ν) * p.ε := by
  have hε := p.ε_pos
  have hA : ‖UnforcedLeray.Cons.C03.Concrete.cA p.period
      (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)‖ ≤ ‖z‖ := by
    have h := UnforcedLeray.Cons.C03.Concrete.norm_amb p.period
      (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)
    have hz' : ‖(z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)‖ = ‖z‖ := rfl
    rw [← hz', h]
    linarith [norm_nonneg (UnforcedLeray.Cons.C03.Concrete.cw p.period
        (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)),
      norm_nonneg (UnforcedLeray.Cons.C03.Concrete.cΔ p.period
        (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)),
      norm_nonneg (UnforcedLeray.Cons.C03.Concrete.cT p.period
        (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period))]
  have hi : |(UnforcedLeray.Cons.C03.Concrete.cA p.period
      (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)) i| ≤ ‖z‖ := by
    have h := PiLp.norm_apply_le (UnforcedLeray.Cons.C03.Concrete.cA p.period
      (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)) i
    rw [Real.norm_eq_abs] at h
    exact h.trans hA
  have hpow : 0 < p.ε ^ (8 / 11 : ℝ) := Real.rpow_pos_of_pos hε _
  have he : p.ε ^ (8 / 11 : ℝ) * p.ε ^ (3 / 11 : ℝ) = p.ε := by
    rw [← Real.rpow_add hε]; norm_num
  unfold Params.coord
  rw [abs_mul, abs_of_pos hpow]
  calc p.ε ^ (8 / 11 : ℝ) * |(UnforcedLeray.Cons.C03.Concrete.cA p.period
        (z : UnforcedLeray.Cons.C03.Concrete.Amb p.period)) i|
      ≤ p.ε ^ (8 / 11 : ℝ) * UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 :=
        mul_le_mul_of_nonneg_left (hi.trans hz) hpow.le
    _ = C0 * (p.ν ^ k0)⁻¹ * Real.exp (m0 / p.ν) * (p.ε ^ (8 / 11 : ℝ) * p.ε ^ (3 / 11 : ℝ)) := by
        unfold UnforcedLeray.Short.IIb.rhoB; ring
    _ = C0 * (p.ν ^ k0)⁻¹ * Real.exp (m0 / p.ν) * p.ε := by rw [he]

private lemma slice_offAxis {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ × Space → F) (h : ContDiffOn ℝ 2 f offAxis) (τ : ℝ) :
    ContDiffOn ℝ 2 (fun w : Space => f (τ, w)) axisᶜ :=
  h.comp (contDiff_const.prodMk contDiff_id).contDiffOn fun _ hw => hw

private lemma slice_smooth {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ × Space → F) (h : ContDiff ℝ ∞ f) (τ : ℝ) :
    ContDiffOn ℝ 2 (fun w : Space => f (τ, w)) axisᶜ :=
  ((h.comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)).contDiffOn

/-- **Sequence-level low-age (`0 < s ≤ 1`) bound on `vJetDens (L.V τ) y`.** -/
theorem vJetDens_V_early_eventually (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ pt : Chart, 0 < pt.1 → pt.1 ≤ 1 →
      vJetDens ((D.level n).V (NearInst.chartTau (D.level n).ε⁻¹ pt))
          (NearInst.chartY (D.level n).ε⁻¹ pt) ≤
        C * (D.level n).ν⁻¹ ^ k * pt.1 * (1 + |pt.2.2|)⁻¹ := by
  obtain ⟨C1, k1, hrc⟩ := ringChartRules D hst
  obtain ⟨C2, k2, htm⟩ := trainMoment D hst
  obtain ⟨C_id, κ, k_id, νa, hC_id, hκ, hνa, _, hdec⟩ :=
    UnforcedLeray.Short.IIb.inletJetDecay D.Sig D.Pl.eigenvalue D.Pl.mode D.Sig_pos
      hst.planar.eigenpair dm dp hst.dm_pos
  obtain ⟨ν₁, hν₁, hS⟩ := UnforcedLeray.Short.IIb.inletJointSmooth D.Sig D.Pl.eigenvalue
    D.Pl.mode D.Sig_pos hst.planar.eigenpair dm dp hst.dm_pos
  have hle1 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  have hρ1 := rhoRep_le_one_eventually D hst
  have hν_small : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n < min νa ν₁ :=
    (retNu_tendsto D.σ₀ hst.omega_ne).eventually (gt_mem_nhds (lt_min hνa hν₁))
  set C_raw := 12 * (2 + |C1|) * max C2 0
  set k_raw := k1 + k2
  set C_inl := 6600 * D.K.C0 * C_id * (min 1 (κ / 3))⁻¹ ^ 3
  set k_inl := D.K.k0 + k_id + 6
  set C := C_raw + C_inl
  set k := max k_raw k_inl
  have hC0 : 0 ≤ C := by
    have hm : 0 < min 1 (κ / 3) := lt_min one_pos (by positivity)
    have hC0' : 0 < D.K.C0 := hst.C0_pos
    positivity
  refine ⟨C, k, hC0, ?_⟩
  filter_upwards [hst.actual, hrc, htm, hle1, hρ1, hν_small] with
    n hn hrc_n htm_n hle1_n hρ1_n hν_n pt hp0 hp1
  set L := D.level n
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hν1 : L.ν ≤ 1 := hle1_n.1
  have hε1 : L.ε ≤ 1 := hle1_n.2
  have hνinv1 : 1 ≤ L.ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hνa_le : L.ν ≤ νa := hν_n.le.trans (min_le_left _ _)
  have hν1_le : L.ν ≤ ν₁ := hν_n.le.trans (min_le_right _ _)
  set p := L.params D.Pl
  have hR1 : 1 ≤ p.R := (one_le_inv₀ hε).2 hε1
  obtain ⟨z, -, hVz, -, hz⟩ := hn.ball
  set τ := NearInst.chartTau L.ε⁻¹ pt
  set y := NearInst.chartY L.ε⁻¹ pt
  have hy_ax : y ∉ axis := by
    intro h
    have hy0 : y 0 = L.ε⁻¹ / Real.sqrt pt.1 := by simp [y, NearInst.chartY]
    have hpos : 0 < L.ε⁻¹ / Real.sqrt pt.1 := div_pos (inv_pos.2 hε) (Real.sqrt_pos.2 hp0)
    rw [← hy0, h.1] at hpos
    exact lt_irrefl _ hpos
  have hraw_c2 : ContDiffOn ℝ 2 (p.raw τ) axisᶜ := by
    have hR := rawU_contDiffOn_offAxis_of p hε (L.train_stream_smooth.of_le (by norm_num))
    exact slice_offAxis (fun x : ℝ × Space => p.raw x.1 x.2) hR τ
  have hinl_c2 : ∀ i : Fin 2, ContDiffOn ℝ 2 (p.inlet i τ) axisᶜ := by
    intro i
    have hi := hS p _ hn.regime hν1_le rfl rfl i
    exact slice_smooth (fun x : ℝ × Space => p.inlet i x.1 x.2) hi τ
  have hsplit := vJetDens_affine_le (L.V τ) (p.raw τ) (fun i => p.inlet i τ)
    (fun i => p.coord z i) axisᶜ y isOpen_compl_axis hy_ax hraw_c2 hinl_c2 fun w => hVz τ w
  -- Bound rawU term
  have hraw_le := vJetDens_rawU_early_le D.Pl L hν1 hε1 hrc_n htm_n.2.1 hp0 hp1
  -- Bound each inlet term
  have hε_le_ρ : Real.exp (D.K.m0 / L.ν) * L.ε ≤ 1 := by
    have hε311 : L.ε ≤ L.ε ^ (3 / 11 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hε hε1 (by norm_num : (3 / 11 : ℝ) ≤ 1)
    calc Real.exp (D.K.m0 / L.ν) * L.ε
        ≤ Real.exp (D.K.m0 / L.ν) * L.ε ^ (3 / 11 : ℝ) :=
          mul_le_mul_of_nonneg_left hε311 (Real.exp_pos _).le
      _ = rhoRep D.K L := by unfold rhoRep; ring
      _ ≤ 1 := hρ1_n
  have hinl_le : ∀ i : Fin 2,
      |p.coord z i| * vJetDens (p.inlet i τ) y ≤
        3300 * D.K.C0 * C_id * (min 1 (κ / 3))⁻¹ ^ 3 * L.ν⁻¹ ^ k_inl *
          pt.1 * (1 + |pt.2.2|)⁻¹ := by
    intro i
    have hpν : p.ν = L.ν := rfl
    have hpε : p.ε = L.ε := rfl
    have hco : |p.coord z i| ≤ D.K.C0 * L.ν⁻¹ ^ D.K.k0 := by
      have hc0 := coord_le_rhoB p D.K.m0 D.K.C0 D.K.k0 z hz i
      rw [hpν, hpε, ← inv_pow] at hc0
      have hC0_pos : 0 < D.K.C0 := hst.C0_pos
      have h1 : D.K.C0 * L.ν⁻¹ ^ D.K.k0 * (Real.exp (D.K.m0 / L.ν) * L.ε) ≤
          D.K.C0 * L.ν⁻¹ ^ D.K.k0 * 1 :=
        mul_le_mul_of_nonneg_left hε_le_ρ (by positivity)
      linarith
    obtain ⟨hsm, hdb⟩ := hdec p _ ⟨hn.regime, hνa_le, rfl, rfl⟩ i
    have hc_eq : p.c = (L.ν ^ 2)⁻¹ := hn.regime.c_eq
    have hexp_eq : Real.exp (-(κ * |pt.2.2| / p.c)) = Real.exp (-(κ * L.ν ^ 2) * |pt.2.2|) := by
      congr 1; rw [hc_eq, div_inv_eq_mul]; ring
    have hsum_b : ∑ l ∈ Finset.range 3, ‖iteratedFDeriv ℝ l (p.inletProfile i) pt‖ ≤
        3 * C_id * L.ν⁻¹ ^ k_id * Real.exp (-(κ * L.ν ^ 2) * |pt.2.2|) := by
      have hb0 := hdb 0 (by norm_num) pt
      have hb1 := hdb 1 (by norm_num) pt
      have hb2 := hdb 2 (by norm_num) pt
      rw [hpν, hexp_eq, ← inv_pow] at hb0 hb1 hb2
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      linarith
    have hnv := vJetDens_Nv_early_le hR1 (p.inletProfile i) hsm.contDiffOn hp0 hp1
    have hinl_jet : vJetDens (p.inlet i τ) y ≤
        3300 * C_id * (min 1 (κ / 3))⁻¹ ^ 3 * L.ν⁻¹ ^ (k_id + 6) * pt.1 * (1 + |pt.2.2|)⁻¹ := by
      have h1 : vJetDens (p.inlet i τ) y ≤
          1100 * pt.1 * (1 + |pt.2.2|) ^ 2 *
            (3 * C_id * L.ν⁻¹ ^ k_id * Real.exp (-(κ * L.ν ^ 2) * |pt.2.2|)) :=
        hnv.trans (mul_le_mul_of_nonneg_left hsum_b (by positivity))
      have habs := sq_exp_neg_le_inv_one_add hκ hν hν1 (abs_nonneg pt.2.2)
      calc vJetDens (p.inlet i τ) y
          ≤ 3300 * C_id * L.ν⁻¹ ^ k_id * pt.1 *
              ((1 + |pt.2.2|) ^ 2 * Real.exp (-(κ * L.ν ^ 2) * |pt.2.2|)) := by linarith
        _ ≤ 3300 * C_id * L.ν⁻¹ ^ k_id * pt.1 *
              ((min 1 (κ / 3))⁻¹ ^ 3 * L.ν⁻¹ ^ 6 * (1 + |pt.2.2|)⁻¹) :=
            mul_le_mul_of_nonneg_left habs (by positivity)
        _ = 3300 * C_id * (min 1 (κ / 3))⁻¹ ^ 3 * L.ν⁻¹ ^ (k_id + 6) * pt.1 *
              (1 + |pt.2.2|)⁻¹ := by
            rw [pow_add]; ring
    have hm : 0 < min 1 (κ / 3) := lt_min one_pos (by positivity)
    have hC0_pos : 0 < D.K.C0 := hst.C0_pos
    calc |p.coord z i| * vJetDens (p.inlet i τ) y
        ≤ (D.K.C0 * L.ν⁻¹ ^ D.K.k0) *
            (3300 * C_id * (min 1 (κ / 3))⁻¹ ^ 3 * L.ν⁻¹ ^ (k_id + 6) * pt.1 *
              (1 + |pt.2.2|)⁻¹) :=
          mul_le_mul hco hinl_jet (vJetDens_nonneg _ _) (by positivity)
      _ = 3300 * D.K.C0 * C_id * (min 1 (κ / 3))⁻¹ ^ 3 * L.ν⁻¹ ^ k_inl *
            pt.1 * (1 + |pt.2.2|)⁻¹ := by
          simp only [k_inl, pow_add]; ring
  have hk_raw : L.ν⁻¹ ^ k_raw ≤ L.ν⁻¹ ^ k := pow_le_pow_right₀ hνinv1 (le_max_left _ _)
  have hk_inl : L.ν⁻¹ ^ k_inl ≤ L.ν⁻¹ ^ k := pow_le_pow_right₀ hνinv1 (le_max_right _ _)
  have hraw' : vJetDens (p.raw τ) y ≤ C_raw * L.ν⁻¹ ^ k * pt.1 * (1 + |pt.2.2|)⁻¹ := by
    have h0 : 0 ≤ C_raw := by positivity
    have hfac : 0 ≤ pt.1 * (1 + |pt.2.2|)⁻¹ := by positivity
    have heq : vJetDens (p.raw τ) y = vJetDens (rawU D.Pl L τ) y := rfl
    rw [heq]
    refine hraw_le.trans ?_
    calc C_raw * L.ν⁻¹ ^ k_raw * pt.1 * (1 + |pt.2.2|)⁻¹
        = C_raw * L.ν⁻¹ ^ k_raw * (pt.1 * (1 + |pt.2.2|)⁻¹) := by ring
      _ ≤ C_raw * L.ν⁻¹ ^ k * (pt.1 * (1 + |pt.2.2|)⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk_raw h0) hfac
      _ = C_raw * L.ν⁻¹ ^ k * pt.1 * (1 + |pt.2.2|)⁻¹ := by ring
  have hinl_sum : ∑ i : Fin 2, |p.coord z i| * vJetDens (p.inlet i τ) y ≤
      C_inl * L.ν⁻¹ ^ k * pt.1 * (1 + |pt.2.2|)⁻¹ := by
    rw [Fin.sum_univ_two]
    have h0 := hinl_le 0
    have h1 := hinl_le 1
    have hC_inl0 : 0 ≤ C_inl := by
      have hm : 0 < min 1 (κ / 3) := lt_min one_pos (by positivity)
      have hC0_pos : 0 < D.K.C0 := hst.C0_pos
      positivity
    have hfac : 0 ≤ pt.1 * (1 + |pt.2.2|)⁻¹ := by positivity
    calc |p.coord z 0| * vJetDens (p.inlet 0 τ) y + |p.coord z 1| * vJetDens (p.inlet 1 τ) y
        ≤ C_inl * L.ν⁻¹ ^ k_inl * (pt.1 * (1 + |pt.2.2|)⁻¹) := by
          simp only [C_inl]; linarith
      _ ≤ C_inl * L.ν⁻¹ ^ k * (pt.1 * (1 + |pt.2.2|)⁻¹) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk_inl hC_inl0) hfac
      _ = C_inl * L.ν⁻¹ ^ k * pt.1 * (1 + |pt.2.2|)⁻¹ := by ring
  calc vJetDens (L.V τ) y
      ≤ vJetDens (p.raw τ) y + ∑ i : Fin 2, |p.coord z i| * vJetDens (p.inlet i τ) y := hsplit
    _ ≤ C_raw * L.ν⁻¹ ^ k * pt.1 * (1 + |pt.2.2|)⁻¹ +
          C_inl * L.ν⁻¹ ^ k * pt.1 * (1 + |pt.2.2|)⁻¹ := add_le_add hraw' hinl_sum
    _ = C * L.ν⁻¹ ^ k * pt.1 * (1 + |pt.2.2|)⁻¹ := by simp only [C]; ring

/-- **Sequence-level high-age (`1 < s`) bound on `12 * coefChgDens (L.V τ) (rawU ...)`.** -/
theorem coefChg_V_late_eventually (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) :
    ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ pt : Chart, 1 < pt.1 →
      12 * coefChgDens ((D.level n).V (NearInst.chartTau (D.level n).ε⁻¹ pt))
          (rawU D.Pl (D.level n) (NearInst.chartTau (D.level n).ε⁻¹ pt))
          (NearInst.chartY (D.level n).ε⁻¹ pt) ≤
        C * (D.level n).ν⁻¹ ^ k * (1 + |pt.2.2 / Real.sqrt pt.1|)⁻¹ := by
  obtain ⟨C3, k3, m1, hm1, hent⟩ := entWPt D hst
  have hle1 := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  have hρ1 := rhoRep_le_one_eventually D hst
  set Ce := max C3 0
  set Cm := (min 1 m1)⁻¹
  have hC0 : 0 ≤ 12 * Ce * Cm := by
    have : 0 < min 1 m1 := lt_min one_pos hm1
    positivity
  refine ⟨12 * Ce * Cm, k3 + 2, hC0, ?_⟩
  filter_upwards [hent, hle1, hρ1] with n hent_n hle1_n hρ1_n pt hp1
  set L := D.level n
  have hp0 : 0 < pt.1 := zero_lt_one.trans hp1
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hν1 : L.ν ≤ 1 := hle1_n.1
  have hε1 : L.ε ≤ 1 := hle1_n.2
  have hε_le_ρ : Real.exp (D.K.m0 / L.ν) * L.ε ≤ 1 := by
    have hε311 : L.ε ≤ L.ε ^ (3 / 11 : ℝ) := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hε hε1 (by norm_num : (3 / 11 : ℝ) ≤ 1)
    calc Real.exp (D.K.m0 / L.ν) * L.ε
        ≤ Real.exp (D.K.m0 / L.ν) * L.ε ^ (3 / 11 : ℝ) :=
          mul_le_mul_of_nonneg_left hε311 (Real.exp_pos _).le
      _ = rhoRep D.K L := by unfold rhoRep; ring
      _ ≤ 1 := hρ1_n
  set c := coefChgDens (L.V (NearInst.chartTau L.ε⁻¹ pt))
    (rawU D.Pl L (NearInst.chartTau L.ε⁻¹ pt)) (NearInst.chartY L.ε⁻¹ pt)
  have hc_exp : c ≤ Ce * L.ν⁻¹ ^ k3 * Real.exp (-(m1 * L.ν ^ 2) * |pt.2.2|) := by
    calc c ≤ C3 * L.ν⁻¹ ^ k3 * (Real.exp (D.K.m0 / L.ν) * L.ε) *
            Real.exp (-(m1 * L.ν ^ 2) * |pt.2.2|) := hent_n pt hp0
      _ ≤ Ce * L.ν⁻¹ ^ k3 * (Real.exp (D.K.m0 / L.ν) * L.ε) *
            Real.exp (-(m1 * L.ν ^ 2) * |pt.2.2|) := by
          have h1 : C3 * L.ν⁻¹ ^ k3 * (Real.exp (D.K.m0 / L.ν) * L.ε) ≤
              Ce * L.ν⁻¹ ^ k3 * (Real.exp (D.K.m0 / L.ν) * L.ε) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left C3 0) (by positivity)) (by positivity)
          exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ Ce * L.ν⁻¹ ^ k3 * 1 * Real.exp (-(m1 * L.ν ^ 2) * |pt.2.2|) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hε_le_ρ (by positivity))
            (Real.exp_pos _).le
      _ = Ce * L.ν⁻¹ ^ k3 * Real.exp (-(m1 * L.ν ^ 2) * |pt.2.2|) := by ring
  have hexp := exp_neg_abs_le_inv_one_add hm1 hν hν1 pt.2.2
  have hinv_le : (1 + |pt.2.2|)⁻¹ ≤ (1 + |pt.2.2 / Real.sqrt pt.1|)⁻¹ := by
    have hsq1 : 1 ≤ Real.sqrt pt.1 := Real.one_le_sqrt.2 hp1.le
    have hdiv : |pt.2.2 / Real.sqrt pt.1| ≤ |pt.2.2| := by
      rw [abs_div, abs_of_pos (zero_lt_one.trans_le hsq1)]
      exact div_le_self (abs_nonneg pt.2.2) hsq1
    exact inv_anti₀ (by positivity) (by linarith)
  calc 12 * c
      ≤ 12 * (Ce * L.ν⁻¹ ^ k3 * ((min 1 m1)⁻¹ * L.ν⁻¹ ^ 2 * (1 + |pt.2.2|)⁻¹)) := by
        have := hc_exp.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
        linarith
    _ = 12 * Ce * Cm * L.ν⁻¹ ^ (k3 + 2) * (1 + |pt.2.2|)⁻¹ := by simp only [Cm]; ring
    _ ≤ 12 * Ce * Cm * L.ν⁻¹ ^ (k3 + 2) * (1 + |pt.2.2 / Real.sqrt pt.1|)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv_le (by positivity)

end UnforcedLeray.Short.PartIIIb.Concrete.VBgSq.JetAux

end
