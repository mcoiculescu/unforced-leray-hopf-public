import UnforcedLeray.Short.PartIIIb.NearInst.Body.Forced
import UnforcedLeray.Short.PartIIIb.NearInst.Body.Proofs.BodyFormNorm

/-!
# `BodyWindowComparison` from the compact-free comparison (source 1692-1722, 3962-3967)

Route: a window cutoff `χ = 1` on the output box (`WindowCutoffExists`, `σ = ε^a`, `H = ε^{-b}`,
`L = L_⊥`) gives `‖1_box (R_ε - R_0) f‖_H ≤ ‖χ (T_ε - T_0) f'‖` after transporting by
`merC ∘ · ∘ cellPt` (which multiplies every norm by `√c`); `Γ` is bounded by a fixed power of
`ν⁻¹ ε^{-(a+b)}`, and `P = 2εc ≤ 1`, `ε ≤ 1` for small `ν`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Body

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete UnforcedLeray.B0223
open UnforcedLeray.B0220 (HSpace measureH Profile)

namespace BodyWindowAux

/-- `mulChi` acts by pointwise multiplication. -/
lemma mulChi_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] (μ : Measure Profile) (χ : Profile → ℝ) (hχ : Measurable χ) {B : ℝ}
    (hB : ∀ p, |χ p| ≤ B) (f : Lp E 2 μ) :
    (UnforcedLeray.Short.PartIIa.mulChi μ χ hχ hB f : Profile → E) =ᵐ[μ] fun p => χ p • f p :=
  MemLp.coeFn_toLp (UnforcedLeray.Short.PartIIa.memLp_chi_smul μ χ hχ hB (Lp.memLp f))

/-- **Box domination.** If `χ = 1` on the box `σ ≤ s < H, |η| ≤ L` and `G = merC ∘ g ∘ cellPt`
then `c ‖1_box g‖² ≤ ‖χ G‖²`. -/
theorem box_le {c : ℝ} (hc : 0 < c) (hH : Masked.CellPtH c) (σ H L : ℝ)
    (χ : Profile → ℝ) (hm : Measurable χ) (hB : ∀ p, |χ p| ≤ 1)
    (hχ1 : ∀ p : Profile, σ ≤ p.1 → p.1 ≤ H → |p.2.2| ≤ L → χ p = 1)
    (g : Hsp c) (G : HSpace c MeridC)
    (hG : (G : Profile → MeridC) =ᵐ[measureH c] fun p => merC ((g : Chart → Merid) (cellPt c p))) :
    c * ‖Delta.outRestr c (Delta.binSet σ H L) g‖ ^ 2 ≤
      ‖UnforcedLeray.Short.PartIIa.mulChi (measureH c) χ hm hB G‖ ^ 2 := by
  set h := Delta.outRestr c (Delta.binSet σ H L) g with hh
  have key : ‖cplxH c hH h‖ ^ 2 = c * ‖h‖ ^ 2 :=
    norm_sq_cellPt hc.le hH merC norm_merC_eq h (cplxH c hH h) (cplxH_ae c hH h)
  have hH' : Measure.map (cellPt c) (measureH c) ≤ ENNReal.ofReal c • ageμ c (-3 / 2) := hH.le
  have hmp := (measurable_cellPt' c).measurePreserving (measureH c)
  have hac := Measure.absolutelyContinuous_of_le_smul hH'
  have hhae : ∀ᵐ x ∂ageμ c (-3 / 2), (h : Chart → Merid) x =
      Delta.ind (Delta.binSet σ H L) x • (g : Chart → Merid) x :=
    Delta.restrLp_ae (Delta.measurableSet_binSet σ H L) g
  have hhp := ae_of_ae_map hmp.aemeasurable (hac.ae_le hhae)
  have hle : ‖cplxH c hH h‖ ≤
      ‖UnforcedLeray.Short.PartIIa.mulChi (measureH c) χ hm hB G‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [cplxH_ae c hH h, mulChi_ae (measureH c) χ hm hB G, hG, hhp] with p h1 h2 h3 h4
    rw [h1, h2, h3, norm_merC_eq, norm_smul, norm_merC_eq, Real.norm_eq_abs, h4, norm_smul,
      Real.norm_eq_abs]
    by_cases hp : cellPt c p ∈ Delta.binSet σ H L
    · have : χ p = 1 := by
        obtain ⟨a1, a2, a3⟩ := hp
        exact hχ1 p a1 a2.le a3
      rw [this]
      simp [Delta.ind, hp]
    · simp [Delta.ind, hp]
      exact mul_nonneg (abs_nonneg _) (norm_nonneg _)
  rw [← key]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-- Small-`ν` facts: `ε ≤ 1`, `ν ≤ 1`, `P = 2εc ≤ 1`, `c = ν⁻²`. -/
theorem regime_small {p : Params} {d dm dp : ℝ} (h : UnforcedLeray.Short.IIb.BgRegime p d dm dp)
    (hν : p.ν ≤ min 1 (dm ^ 3 / 12)) : p.ε ≤ 1 ∧ p.ν ≤ 1 ∧ p.period ≤ 1 := by
  have hν0 := p.ν_pos
  have hdm := h.dm_pos
  have hd : 0 < d := lt_of_lt_of_le hdm h.dm_le
  have hν1 : p.ν ≤ 1 := le_trans hν (min_le_left _ _)
  have hν2 : p.ν ≤ dm ^ 3 / 12 := le_trans hν (min_le_right _ _)
  have hε1 : p.ε ≤ 1 := by
    rw [h.eps_eq, Real.exp_le_one_iff]
    exact (div_neg_of_neg_of_pos (by linarith) hν0).le
  refine ⟨hε1, hν1, ?_⟩
  -- exp (d/ν) ≥ (d/ν)^3 / 6
  have hx : 0 ≤ d / p.ν := div_nonneg hd.le hν0.le
  have he := Real.pow_div_factorial_le_exp (d / p.ν) hx 3
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6] at he
  have hexp : p.ε = (Real.exp (d / p.ν))⁻¹ := by
    rw [h.eps_eq, ← Real.exp_neg]; congr 1; ring
  have hdm3 : dm ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ hdm.le h.dm_le 3
  have hcc : p.c = (p.ν ^ 2)⁻¹ := h.c_eq
  unfold Params.period
  rw [hcc, hexp]
  have hE : 0 < Real.exp (d / p.ν) := Real.exp_pos _
  rw [show 2 * (Real.exp (d / p.ν))⁻¹ * (p.ν ^ 2)⁻¹ = 2 / (Real.exp (d / p.ν) * p.ν ^ 2) by
    field_simp]
  rw [div_le_one (by positivity)]
  have h3 : (d / p.ν) ^ 3 / 6 * p.ν ^ 2 ≤ Real.exp (d / p.ν) * p.ν ^ 2 :=
    mul_le_mul_of_nonneg_right he (by positivity)
  have h4 : (d / p.ν) ^ 3 / 6 * p.ν ^ 2 = d ^ 3 / (6 * p.ν) := by
    field_simp
  rw [h4] at h3
  have h5 : 2 ≤ d ^ 3 / (6 * p.ν) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hdm3]
  linarith

/-- The polynomial bound on `Γ`. -/
theorem gamma_le {ν ε a b Cperp Ccut : ℝ} {kc : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (ha : 0 < a) (hb : 0 < b) {c : ℝ} (hc : c = (ν ^ 2)⁻¹) {L : ℝ}
    (hL : L = max (Delta.transL Cperp c ν (ε ^ (-b))) 0) {χ χ1 : Profile → ℝ}
    (hcut : UnforcedLeray.Short.PartIIa.cNorm8 χ + UnforcedLeray.Short.PartIIa.cNorm8 χ1 ≤
      Ccut * ((ε ^ a)⁻¹ + ε ^ (-b) + L + 2) ^ kc) :
    UnforcedLeray.Short.PartIIa.Gamma ν c (ε ^ a / 2) (2 * ε ^ (-b)) (2 * L + 1) (1 / 4) (1 / 4)
        χ χ1 ≤
      (30 + |Ccut| * 7 ^ kc) *
        ((1 + |Cperp|) * ν⁻¹ ^ 3 * ε ^ (-(a + b))) ^ (kc + 1) := by
  set V : ℝ := ν⁻¹ with hV
  set E : ℝ := ε ^ (-(a + b)) with hE
  have hV1 : 1 ≤ V := one_le_inv_iff₀.2 ⟨hν, hν1⟩
  have hE1 : 1 ≤ E := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)
  have hHE : ε ^ (-b) ≤ E := Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have hH1 : 1 ≤ ε ^ (-b) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)
  have hσE : (ε ^ a)⁻¹ ≤ E := by
    rw [← Real.rpow_neg hε.le]
    exact Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have hσ0 : 0 < ε ^ a := Real.rpow_pos_of_pos hε a
  have hsq : Real.sqrt (ε ^ (-b)) ≤ ε ^ (-b) :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hcV : c = V ^ 2 := by rw [hc, hV, inv_pow]
  have hcν : c / ν = V ^ 3 := by rw [hcV, hV]; field_simp
  have hCp : 0 ≤ |Cperp| := abs_nonneg _
  set A : ℝ := (1 + |Cperp|) * V ^ 3 * E with hA
  have hV3 : V ≤ V ^ 3 := by
    calc V = V ^ 1 := (pow_one V).symm
      _ ≤ V ^ 3 := pow_le_pow_right₀ hV1 (by norm_num)
  have hV2 : V ^ 2 ≤ V ^ 3 := pow_le_pow_right₀ hV1 (by norm_num)
  have hV3' : 1 ≤ V ^ 3 := one_le_pow₀ hV1
  have hC1 : 1 ≤ 1 + |Cperp| := by linarith
  have hT1 : V ^ 3 ≤ (1 + |Cperp|) * V ^ 3 := le_mul_of_one_le_left (by linarith) hC1
  have hT1' : 1 ≤ (1 + |Cperp|) * V ^ 3 := le_trans hV3' hT1
  have hEA : E ≤ A := by
    rw [hA]; exact le_mul_of_one_le_left (by linarith) hT1'
  have hTE : V ^ 3 ≤ V ^ 3 * E := le_mul_of_one_le_right (by linarith) hE1
  have hTA : (1 + |Cperp|) * V ^ 3 ≤ A := by
    rw [hA]; exact le_mul_of_one_le_right (by linarith) hE1
  have hA1 : 1 ≤ A := le_trans hT1' hTA
  have hVA : V ≤ A := by linarith
  have hV2A : V ^ 2 ≤ A := by linarith
  have hLnn : 0 ≤ L := by rw [hL]; exact le_max_right _ _
  have hVE : 1 ≤ V ^ 3 * E := le_trans hV3' hTE
  have hLA : L ≤ 3 * A := by
    rw [hL]
    refine max_le ?_ (by linarith)
    unfold Delta.transL
    rw [hcν]
    have h1 : Cperp * (V ^ 3 + Real.sqrt (ε ^ (-b)) + 1) ≤
        |Cperp| * (V ^ 3 + Real.sqrt (ε ^ (-b)) + 1) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have hEV : E ≤ V ^ 3 * E := le_mul_of_one_le_left (by linarith) hV3'
    have h2 : V ^ 3 + Real.sqrt (ε ^ (-b)) + 1 ≤ 3 * (V ^ 3 * E) := by linarith
    have h3 : |Cperp| * (V ^ 3 + Real.sqrt (ε ^ (-b)) + 1) ≤ |Cperp| * (3 * (V ^ 3 * E)) :=
      mul_le_mul_of_nonneg_left h2 hCp
    rw [hA]
    linarith
  have hcinv : c⁻¹ ≤ 1 := by
    rw [hc, inv_inv]; exact pow_le_one₀ hν.le hν1
  have hbox : UnforcedLeray.Short.PartIIa.GammaBox ν c (ε ^ a / 2) (2 * ε ^ (-b)) (2 * L + 1)
      (1 / 4) (1 / 4) ≤ 30 * A := by
    unfold UnforcedLeray.Short.PartIIa.GammaBox
    have : (ε ^ a / 2)⁻¹ = 2 * (ε ^ a)⁻¹ := by field_simp
    rw [this]
    have h14 : ((1 : ℝ) / 4)⁻¹ = 4 := by norm_num
    rw [h14]
    have hνV : ν⁻¹ = V := rfl
    rw [hνV]
    linarith
  have hX : (ε ^ a)⁻¹ + ε ^ (-b) + L + 2 ≤ 7 * A := by linarith
  have hX0 : 0 ≤ (ε ^ a)⁻¹ + ε ^ (-b) + L + 2 := by
    have : 0 ≤ (ε ^ a)⁻¹ := inv_nonneg.2 hσ0.le
    linarith
  have hcutA : UnforcedLeray.Short.PartIIa.cNorm8 χ + UnforcedLeray.Short.PartIIa.cNorm8 χ1 ≤
      |Ccut| * 7 ^ kc * A ^ kc := by
    refine le_trans hcut ?_
    calc Ccut * ((ε ^ a)⁻¹ + ε ^ (-b) + L + 2) ^ kc ≤
        |Ccut| * ((ε ^ a)⁻¹ + ε ^ (-b) + L + 2) ^ kc :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hX0 _)
      _ ≤ |Ccut| * (7 * A) ^ kc :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0 hX kc) (abs_nonneg _)
      _ = |Ccut| * 7 ^ kc * A ^ kc := by rw [mul_pow]; ring
  unfold UnforcedLeray.Short.PartIIa.Gamma
  have hAk : A ^ kc ≤ A ^ (kc + 1) := pow_le_pow_right₀ hA1 (by omega)
  have hA1k : A ≤ A ^ (kc + 1) := by
    calc A = A ^ 1 := (pow_one A).symm
      _ ≤ A ^ (kc + 1) := pow_le_pow_right₀ hA1 (by omega)
  have h7 : 0 ≤ |Ccut| * 7 ^ kc := by positivity
  calc _ ≤ 30 * A + |Ccut| * 7 ^ kc * A ^ kc := by linarith
    _ ≤ 30 * A ^ (kc + 1) + |Ccut| * 7 ^ kc * A ^ (kc + 1) := by
        have := mul_le_mul_of_nonneg_left hAk h7
        linarith
    _ = (30 + |Ccut| * 7 ^ kc) * A ^ (kc + 1) := by ring

end BodyWindowAux

open BodyWindowAux in
theorem bodyWindowComparison_of
    (hCF : UnforcedLeray.Short.PartIIa.NearCompactFreeComparison) (hCut : WindowCutoffExists)
    (hH : ∀ c : ℝ, 0 < c → Masked.CellPtH c) (hHi : ∀ c : ℝ, 0 < c → Masked.CellPtInvH c) :
    BodyWindowComparison := by
  obtain ⟨kCF, CCF, hCCF, hCF⟩ := hCF
  obtain ⟨Ccut, kc, hCut⟩ := hCut
  intro Kset _ hKsub dm dp hdm
  refine ⟨(kc + 1) * kCF, fun a b Cperp ha hb hb1 => ?_⟩
  set K : ℕ := (kc + 1) * kCF with hK
  set C2 : ℝ := 30 + |Ccut| * 7 ^ kc with hC2
  have hC20 : 0 ≤ C2 := by positivity
  refine ⟨CCF * C2 ^ kCF * (1 + |Cperp|) ^ K, 3 * K, min 1 (dm ^ 3 / 12), ?_, ?_⟩
  · exact lt_min one_pos (by positivity)
  intro p d hreg hν μ hμ Reps R0 hR hR0 f
  obtain ⟨hε1, hν1, hP1⟩ := regime_small hreg hν
  have hν0 := p.ν_pos
  have hε0 := p.ε_pos
  have hc0 := p.c_pos
  have hμ' := hKsub hμ
  -- the window parameters
  set σ : ℝ := p.ε ^ a with hσdef
  set H : ℝ := p.ε ^ (-b) with hHdef
  set L : ℝ := max (Delta.transL Cperp p.c p.ν H) 0 with hLdef
  have hσ0 : 0 < σ := Real.rpow_pos_of_pos hε0 a
  have hσ1 : σ ≤ 1 := Real.rpow_le_one hε0.le hε1 ha.le
  have hH1 : 1 ≤ H := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 hε1 (by linarith)
  have hL0 : 0 ≤ L := le_max_right _ _
  obtain ⟨χ, χ1, hnear, hlarge, hmeas, habs, hone, hnorm⟩ :=
    hCut p.c σ H L hc0 hσ0 (le_trans hσ1 hH1) hL0
  -- the comparison on the cell
  have hP : (p.period : ℝ) = 2 * p.ε * p.c := rfl
  have hCFapp := (hCF p.ν p.c (σ / 2) (2 * H) (2 * L + 1) (1 / 4) (1 / 4) χ χ1 p.ν_pos hc0
    (by positivity) (by linarith) (by linarith) (by norm_num) hnear hlarge hmeas 1 habs
    p.ε p.ε_pos hε1 p.period hP hP1 (μ : ℂ)
    (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hμ'.1]; exact hμ'.2.le)
    (by rw [Complex.ofReal_re]; linarith [hμ'.1])).1
  set f' := cplxH p.c (hH p.c hc0) f with hf'
  have hGae : (((UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl
        (μ : ℂ) - UnforcedLeray.Short.PartIIa.T0flat p.c_pos p.ν (μ : ℂ)) f' : HSpace p.c MeridC) :
        Profile → MeridC) =ᵐ[measureH p.c] fun q => merC (((Reps - R0) f : Hsp p.c) (cellPt p.c q)) := by
    have e1 := hR f f' (cplxH_ae p.c (hH p.c hc0) f)
    have e2 := hR0 f f' (cplxH_ae p.c (hH p.c hc0) f)
    have e3 := Lp.coeFn_sub (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos
      p.c_pos rfl (μ : ℂ) f') (UnforcedLeray.Short.PartIIa.T0flat p.c_pos p.ν (μ : ℂ) f')
    have hmp := (measurable_cellPt' p.c).measurePreserving (measureH p.c)
    have hH' : Measure.map (cellPt p.c) (measureH p.c) ≤
        ENNReal.ofReal p.c • ageμ p.c (-3 / 2) := (hH p.c hc0).le
    have hac := Measure.absolutelyContinuous_of_le_smul hH'
    have e4 := ae_of_ae_map hmp.aemeasurable (hac.ae_le (Lp.coeFn_sub (Reps f) (R0 f)))
    filter_upwards [e1, e2, e3, e4] with q h1 h2 h3 h4
    rw [sub_apply, h3, Pi.sub_apply, h1, h2]
    rw [sub_apply, h4]
    ext i
    simp [merC]
  have hbox := box_le hc0 (hH p.c hc0) σ H (Delta.transL Cperp p.c p.ν H) χ hmeas habs
    (fun q h1 h2 h3 => hone q h1 h2 (le_trans h3 (le_max_left _ _))) ((Reps - R0) f) _ hGae
  -- squared norm of the input
  have hkey : ‖f'‖ ^ 2 = p.c * ‖f‖ ^ 2 :=
    norm_sq_cellPt hc0.le (hH p.c hc0) merC norm_merC_eq f f' (cplxH_ae p.c (hH p.c hc0) f)
  set Xv : ℝ := CCF * UnforcedLeray.Short.PartIIa.Gamma p.ν p.c (σ / 2) (2 * H) (2 * L + 1)
    (1 / 4) (1 / 4) χ χ1 ^ kCF * p.ε ^ (1 / 14 : ℝ) with hXv
  have hΓ0 : 0 ≤ UnforcedLeray.Short.PartIIa.Gamma p.ν p.c (σ / 2) (2 * H) (2 * L + 1)
      (1 / 4) (1 / 4) χ χ1 := by
    unfold UnforcedLeray.Short.PartIIa.Gamma UnforcedLeray.Short.PartIIa.GammaBox
    have h1 : 0 ≤ UnforcedLeray.Short.PartIIa.cNorm8 χ :=
      Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ UnforcedLeray.Short.PartIIa.cNorm8 χ1 :=
      Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
    have : 0 ≤ (σ / 2)⁻¹ := inv_nonneg.2 (by positivity)
    have : 0 ≤ p.c⁻¹ := inv_nonneg.2 hc0.le
    have : 0 ≤ p.ν⁻¹ := inv_nonneg.2 hν0.le
    linarith
  have hX0 : 0 ≤ Xv := by positivity
  have hfin : ‖Delta.outRestr p.c (Delta.binSet σ H (Delta.transL Cperp p.c p.ν H))
      ((Reps - R0) f)‖ ≤ Xv * ‖f‖ := by
    have h2 := hCFapp f'
    have h3 : p.c * ‖Delta.outRestr p.c (Delta.binSet σ H (Delta.transL Cperp p.c p.ν H))
        ((Reps - R0) f)‖ ^ 2 ≤ (Xv * ‖f'‖) ^ 2 :=
      le_trans hbox (pow_le_pow_left₀ (norm_nonneg _) h2 2)
    rw [mul_pow, hkey] at h3
    have h4 : p.c * ‖Delta.outRestr p.c (Delta.binSet σ H (Delta.transL Cperp p.c p.ν H))
        ((Reps - R0) f)‖ ^ 2 ≤ p.c * (Xv * ‖f‖) ^ 2 := by
      calc _ ≤ Xv ^ 2 * (p.c * ‖f‖ ^ 2) := h3
        _ = p.c * (Xv * ‖f‖) ^ 2 := by ring
    have h5 := le_of_mul_le_mul_left h4 hc0
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h5
  -- the bound on `Γ`
  have hcut' : UnforcedLeray.Short.PartIIa.cNorm8 χ + UnforcedLeray.Short.PartIIa.cNorm8 χ1 ≤
      Ccut * ((p.ε ^ a)⁻¹ + p.ε ^ (-b) + L + 2) ^ kc := hnorm
  have hΓ := gamma_le (Ccut := Ccut) (kc := kc) hν0 hν1 hε0 hε1 ha hb hreg.c_eq rfl hcut'
  have hΓk := pow_le_pow_left₀ hΓ0 hΓ kCF
  set V : ℝ := p.ν⁻¹ with hV
  have hE0 : 0 ≤ p.ε ^ (-(a + b)) := (Real.rpow_pos_of_pos hε0 _).le
  have hEK : (p.ε ^ (-(a + b))) ^ K = p.ε ^ (-(a + b) * (K : ℝ)) :=
    (Real.rpow_mul_natCast hε0.le _ K).symm
  have hAK : (((1 + |Cperp|) * V ^ 3 * p.ε ^ (-(a + b))) ^ (kc + 1)) ^ kCF =
      (1 + |Cperp|) ^ K * V ^ (3 * K) * p.ε ^ (-(a + b) * (K : ℝ)) := by
    rw [← pow_mul, mul_pow, mul_pow, ← pow_mul, ← hEK]
  have hXv : Xv ≤ CCF * C2 ^ kCF * (1 + |Cperp|) ^ K * V ^ (3 * K) *
      p.ε ^ (1 / 14 - (K : ℝ) * (a + b)) := by
    have h6 : UnforcedLeray.Short.PartIIa.Gamma p.ν p.c (σ / 2) (2 * H) (2 * L + 1)
        (1 / 4) (1 / 4) χ χ1 ^ kCF ≤ C2 ^ kCF *
        (((1 + |Cperp|) * V ^ 3 * p.ε ^ (-(a + b))) ^ (kc + 1)) ^ kCF := by
      rw [← mul_pow]; exact hΓk
    have h7 : p.ε ^ (1 / 14 - (K : ℝ) * (a + b)) =
        p.ε ^ (-(a + b) * (K : ℝ)) * p.ε ^ (1 / 14 : ℝ) := by
      rw [← Real.rpow_add hε0]; congr 1; ring
    rw [h7, hXv]
    calc CCF * UnforcedLeray.Short.PartIIa.Gamma p.ν p.c (σ / 2) (2 * H) (2 * L + 1)
          (1 / 4) (1 / 4) χ χ1 ^ kCF * p.ε ^ (1 / 14 : ℝ) ≤
        CCF * (C2 ^ kCF * (((1 + |Cperp|) * V ^ 3 * p.ε ^ (-(a + b))) ^ (kc + 1)) ^ kCF) *
          p.ε ^ (1 / 14 : ℝ) := by
          gcongr
      _ = _ := by rw [hAK]; ring
  calc _ ≤ Xv * ‖f‖ := hfin
    _ ≤ _ := mul_le_mul_of_nonneg_right (by
        refine le_trans hXv (le_of_eq ?_)
        ring) (norm_nonneg _)

end UnforcedLeray.Short.PartIIIb.NearInst.Body
