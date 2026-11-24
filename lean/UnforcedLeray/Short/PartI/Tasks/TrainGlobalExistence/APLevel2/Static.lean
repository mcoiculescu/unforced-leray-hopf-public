import UnforcedLeray.Short.PartI.Sub.PartI_T04_9
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.GN
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APElliptic
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEllipticC

/-!
# Part I, `PartI:T04/9/2`, target `apLevel2Static`: the static trilinear estimate

Source of record: `the November 2 reference manuscript`, lines 285-288.
Route: Hölder `∫|Dω|²|Dv| ≤ (∫|Dω|⁴)^{1/2} (∫|Dv|²)^{1/2}` (with `∫|Dv|² ≤ K₀ A`, `apElliptic`,
`j = 0`), `∫|Dω|⁴ ≤ C⁴ A² ∫|D²ω|²` (`cylGN_proof`, `m = 2`, `l = 1`, `‖ω‖_∞ ≤ A`), then the
AM-GM step `4S ≤ νY + 4L/ν` from `S² ≤ L Y`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- The curl of a `c`-periodic field is `c`-periodic. -/
theorem apL2s_curl_isPeriodic {c : ℝ} {u : Plane → Vec} (hu : Cyl.IsPeriodic c u) :
    Cyl.IsPeriodic c (Cyl.curl u) := by
  rintro ⟨z1, z2⟩
  show Cyl.curl u (z1 + c, z2) = Cyl.curl u (z1, z2)
  have hP1 : Cyl.partialQ (fun w => u w 1) (z1 + c, z2)
      = Cyl.partialQ (fun w => u w 1) (z1, z2) := by
    show deriv (fun q : ℝ => u (q, z2) 1) (z1 + c) = deriv (fun q : ℝ => u (q, z2) 1) z1
    have hGp : ∀ x : ℝ, u (x + c, z2) 1 = u (x, z2) 1 := fun x => by
      have h := hu (x, z2)
      dsimp only at h
      rw [h]
    have hfun : (fun x : ℝ => u (x + c, z2) 1) = (fun x : ℝ => u (x, z2) 1) := funext hGp
    have key : deriv (fun x : ℝ => u (x + c, z2) 1) z1
        = deriv (fun x : ℝ => u (x, z2) 1) (z1 + c) :=
      deriv_comp_add_const (fun x : ℝ => u (x, z2) 1) c z1
    rw [hfun] at key
    exact key.symm
  have hP2 : Cyl.partialEta (fun w => u w 0) (z1 + c, z2)
      = Cyl.partialEta (fun w => u w 0) (z1, z2) := by
    show deriv (fun η : ℝ => u (z1 + c, η) 0) z2 = deriv (fun η : ℝ => u (z1, η) 0) z2
    have hE : (fun η : ℝ => u (z1 + c, η) 0) = (fun η : ℝ => u (z1, η) 0) := funext fun η => by
      have h := hu (z1, η)
      dsimp only at h
      rw [h]
    rw [hE]
  unfold Cyl.curl
  rw [hP1, hP2]

/-- Jets of a smooth field lie in `L²(cell)` once its `L²(cell)` jets are finite. -/
theorem apL2s_memLp_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}
    {u : Plane → E} (hu : ContDiff ℝ ∞ u) (j : ℕ)
    (hL : IntegrableOn (fun z => ‖iteratedFDeriv ℝ j u z‖ ^ 2) (Cyl.cell c)) :
    MemLp (fun z => iteratedFDeriv ℝ j u z) 2 (Cyl.cellμ c) :=
  (memLp_two_iff_integrable_sq_norm
    (hu.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).aestronglyMeasurable).2 hL

/-- `L²(cell)` jets of the curl are controlled by the `(j+1)`-jets of the field. -/
theorem apL2s_curl_integrableOn {c : ℝ} {u : Plane → Vec} (hu : ContDiff ℝ ∞ u)
    (hL : ∀ i : ℕ, IntegrableOn (fun z => ‖iteratedFDeriv ℝ i u z‖ ^ 2) (Cyl.cell c)) (j : ℕ) :
    IntegrableOn (fun z => ‖iteratedFDeriv ℝ j (Cyl.curl u) z‖ ^ 2) (Cyl.cell c) := by
  have hc : Continuous (fun z => ‖iteratedFDeriv ℝ j (Cyl.curl u) z‖ ^ 2) :=
    ((APEllipticCaux.curl_contDiff hu).continuous_iteratedFDeriv (m := j)
      (by exact_mod_cast le_top)).norm.pow 2
  refine Integrable.mono' (Integrable.const_mul (hL (j + 1)) (‖APEllipticCaux.lam‖ ^ 2))
    hc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  have h1 := APEllipticCaux.iteratedFDeriv_curl_le hu j z
  show ‖‖iteratedFDeriv ℝ j (Cyl.curl u) z‖ ^ 2‖
    ≤ ‖APEllipticCaux.lam‖ ^ 2 * ‖iteratedFDeriv ℝ (j + 1) u z‖ ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg ‖iteratedFDeriv ℝ j (Cyl.curl u) z‖)]
  calc ‖iteratedFDeriv ℝ j (Cyl.curl u) z‖ ^ 2
      ≤ (‖APEllipticCaux.lam‖ * ‖iteratedFDeriv ℝ (j + 1) u z‖) ^ 2 := by gcongr
    _ = ‖APEllipticCaux.lam‖ ^ 2 * ‖iteratedFDeriv ℝ (j + 1) u z‖ ^ 2 := by ring

theorem apL2s_sq_rpow_half {x : ℝ} (hx : 0 ≤ x) : (x ^ (1/2 : ℝ)) ^ 2 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- The algebraic Young step: `S² ≤ L Y` gives `4S ≤ (ν/4) Y + 16 L/ν`. -/
theorem apL2s_amgm {S Y L ν : ℝ} (hS : 0 ≤ S) (hY : 0 ≤ Y) (hL : 0 ≤ L) (hν : 0 < ν)
    (h : S ^ 2 ≤ L * Y) : 4 * S ≤ (ν / 4) * Y + 16 * L / ν := by
  have key : 16 * S * ν ≤ ν ^ 2 * Y + 64 * L := by
    rcases hY.eq_or_lt with h0 | hpos
    · subst h0
      have hS0 : S = 0 := by nlinarith [sq_nonneg S]
      subst hS0
      nlinarith
    · nlinarith [sq_nonneg (ν * Y - 8 * S), mul_pos hν hpos]
  have hq : 16 * L / ν * ν = 16 * L := div_mul_cancel₀ (16 * L) hν.ne'
  nlinarith [hq, key, hν]

/-- **Target `apLevel2Static`** (lines 285-288): the static estimate of the trilinear term. -/
theorem apLevel2Static : APLevel2Static := by
  obtain ⟨K0, hK0, hE⟩ := apElliptic 0
  obtain ⟨Cm, hCm, hGN⟩ := cylGN_proof 2 (by norm_num)
  refine ⟨16 * (K0 * Cm ^ 4), mul_nonneg (by norm_num) (mul_nonneg hK0 (pow_nonneg hCm 4)), ?_⟩
  intro ν c T A v p hν hc hcls r hr hA0 hsup
  have hA : 0 ≤ A := le_trans (abs_nonneg _) (hsup 0)
  have hu : ContDiff ℝ ∞ (v r) := by
    have h := hcls.classical.smooth_v.comp_contDiff
      ((contDiff_const : ContDiff ℝ ∞ (fun _ : Plane => r)).prodMk contDiff_id :
        ContDiff ℝ ∞ (fun z : Plane => ((r, z) : ℝ × Plane)))
      (fun z => (⟨hr, mem_univ z⟩ : ((r, z) : ℝ × Plane) ∈ Icc (0 : ℝ) T ×ˢ univ))
    exact h
  have hper : Cyl.IsPeriodic c (v r) := hcls.classical.periodic_v r hr
  have hdiv : ∀ z, Cyl.divergence (v r) z = 0 := hcls.classical.solenoidal r hr
  have hbdd : ∀ i : ℕ, ∃ M : ℝ, ∀ z, ‖iteratedFDeriv ℝ i (v r) z‖ ≤ M := fun i => by
    obtain ⟨M, hM⟩ := hcls.bounded i
    exact ⟨M, fun z => hM r hr z⟩
  have hL : ∀ i : ℕ, IntegrableOn (fun z => ‖iteratedFDeriv ℝ i (v r) z‖ ^ 2) (Cyl.cell c) :=
    fun i => by
      obtain ⟨K, hK⟩ := hcls.jet_l2 i
      exact (hK r hr).1
  have hA0' : ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 0 (Cyl.curl (v r)) z‖ ^ 2 ≤ A := hA0
  have hX : ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 1 (v r) z‖ ^ 2 ≤ K0 * A :=
    le_trans (hE c hc (v r) hu hper hdiv hbdd hL) (mul_le_mul_of_nonneg_left hA0' hK0)
  have hf : ContDiff ℝ ∞ (Cyl.curl (v r)) := APEllipticCaux.curl_contDiff hu
  have hfper : Cyl.IsPeriodic c (Cyl.curl (v r)) := apL2s_curl_isPeriodic hper
  have hfL : ∀ j : ℕ, MemLp (Train.jet j (Cyl.curl (v r))) 2 (Cyl.cellμ c) := fun j =>
    apL2s_memLp_jet hf j (apL2s_curl_integrableOn hu hL j)
  have hG4 : eLpNorm (Train.jet 1 (Cyl.curl (v r))) (ENNReal.ofReal 4) (Cyl.cellμ c) ≤
      ENNReal.ofReal Cm * (⨆ z, ‖Cyl.curl (v r) z‖ₑ) ^ (1/2 : ℝ) *
        Train.cellL2 c (Train.jet 2 (Cyl.curl (v r))) ^ (1/2 : ℝ) := by
    have h := hGN c hc (Cyl.curl (v r)) hf hfper hfL 1 le_rfl (by norm_num)
    convert h using 3 <;> norm_num
  have hsupE : (⨆ z, ‖Cyl.curl (v r) z‖ₑ) ≤ ENNReal.ofReal A := iSup_le fun z => by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hsup z)
  have hY0 : 0 ≤ vortJet c 2 v r := by
    unfold vortJet
    exact integral_nonneg fun z => sq_nonneg _
  have hYcell : Train.cellL2 c (Train.jet 2 (Cyl.curl (v r)))
      = ENNReal.ofReal (vortJet c 2 v r ^ (1/2 : ℝ)) := by
    have hm := (hfL 2).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
    rw [ENNReal.toReal_ofNat] at hm
    have hI : ∫ z, ‖Train.jet 2 (Cyl.curl (v r)) z‖ ^ (2:ℝ) ∂(Cyl.cellμ c)
        = vortJet c 2 v r := by
      unfold vortJet
      simp only [Real.rpow_two]
      rfl
    unfold Train.cellL2
    rw [hm, hI, one_div]
  have hgmem : MemLp (Train.jet 1 (Cyl.curl (v r))) (ENNReal.ofReal 4) (Cyl.cellμ c) := by
    refine ⟨(hf.continuous_iteratedFDeriv (m := 1) (by exact_mod_cast le_top)).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt hG4 (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_) ?_)
    · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsupE)
    · rw [hYcell]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ∫ z, ‖Train.jet 1 (Cyl.curl (v r)) z‖ ^ (4:ℝ) ∂(Cyl.cellμ c) :=
    ⟨_, rfl⟩
  have hLHS : eLpNorm (Train.jet 1 (Cyl.curl (v r))) (ENNReal.ofReal 4) (Cyl.cellμ c)
      = ENNReal.ofReal (Z ^ (4⁻¹ : ℝ)) := by
    rw [hgmem.eLpNorm_eq_integral_rpow_norm (by simp) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 4), hZ]
  have hA12 : (⨆ z, ‖Cyl.curl (v r) z‖ₑ) ^ (1/2 : ℝ) ≤ ENNReal.ofReal (A ^ (1/2 : ℝ)) := by
    calc (⨆ z, ‖Cyl.curl (v r) z‖ₑ) ^ (1/2 : ℝ) ≤ (ENNReal.ofReal A) ^ (1/2 : ℝ) :=
          ENNReal.rpow_le_rpow hsupE (by norm_num)
      _ = ENNReal.ofReal (A ^ (1/2 : ℝ)) := ENNReal.ofReal_rpow_of_nonneg hA (by norm_num)
  have hR : ENNReal.ofReal Cm * (⨆ z, ‖Cyl.curl (v r) z‖ₑ) ^ (1/2 : ℝ) *
      Train.cellL2 c (Train.jet 2 (Cyl.curl (v r))) ^ (1/2 : ℝ)
      ≤ ENNReal.ofReal (Cm * A ^ (1/2 : ℝ) * (vortJet c 2 v r ^ (1/2 : ℝ)) ^ (1/2 : ℝ)) := by
    have hY12 : Train.cellL2 c (Train.jet 2 (Cyl.curl (v r))) ^ (1/2 : ℝ)
        = ENNReal.ofReal ((vortJet c 2 v r ^ (1/2 : ℝ)) ^ (1/2 : ℝ)) := by
      rw [hYcell, ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hY0 _) (by norm_num)]
    rw [hY12, ENNReal.ofReal_mul (mul_nonneg hCm (Real.rpow_nonneg hA _)),
      ENNReal.ofReal_mul hCm]
    gcongr
  have hWnn : 0 ≤ Cm * A ^ (1/2 : ℝ) * (vortJet c 2 v r ^ (1/2 : ℝ)) ^ (1/2 : ℝ) :=
    mul_nonneg (mul_nonneg hCm (Real.rpow_nonneg hA _))
      (Real.rpow_nonneg (Real.rpow_nonneg hY0 _) _)
  have hfin : ENNReal.ofReal (Z ^ (4⁻¹ : ℝ))
      ≤ ENNReal.ofReal (Cm * A ^ (1/2 : ℝ) * (vortJet c 2 v r ^ (1/2 : ℝ)) ^ (1/2 : ℝ)) := by
    rw [← hLHS]
    exact hG4.trans hR
  have hreal : Z ^ (4⁻¹ : ℝ) ≤ Cm * A ^ (1/2 : ℝ) * (vortJet c 2 v r ^ (1/2 : ℝ)) ^ (1/2 : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff hWnn).1 hfin
  have hZnn : 0 ≤ Z := by
    rw [hZ]
    exact integral_nonneg fun z => Real.rpow_nonneg (norm_nonneg _) _
  have hpA : (A ^ (1/2 : ℝ)) ^ 4 = A ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA, ← Real.rpow_natCast]
    norm_num
  have hpY : ((vortJet c 2 v r ^ (1/2 : ℝ)) ^ (1/2 : ℝ)) ^ 4 = vortJet c 2 v r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY0, ← Real.rpow_mul hY0]
    norm_num
  have hZle : Z ≤ Cm ^ 4 * A ^ 2 * vortJet c 2 v r := by
    have h4 : (Z ^ (4⁻¹ : ℝ)) ^ 4 = Z := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hZnn]
      norm_num
    calc Z = (Z ^ (4⁻¹ : ℝ)) ^ 4 := h4.symm
      _ ≤ (Cm * A ^ (1/2 : ℝ) * (vortJet c 2 v r ^ (1/2 : ℝ)) ^ (1/2 : ℝ)) ^ 4 :=
          pow_le_pow_left₀ (Real.rpow_nonneg hZnn _) hreal 4
      _ = Cm ^ 4 * A ^ 2 * vortJet c 2 v r := by
          rw [mul_pow, mul_pow, hpA, hpY]
  -- Hölder inequality for `∫ |Dω|² |Dv|`.
  have hbmem : MemLp (fun z => iteratedFDeriv ℝ 1 (v r) z) 2 (Cyl.cellμ c) :=
    apL2s_memLp_jet hu 1 (hL 1)
  have hgsq : MemLp (fun z => ‖Train.jet 1 (Cyl.curl (v r)) z‖ ^ 2) 2 (Cyl.cellμ c) := by
    refine (memLp_two_iff_integrable_sq_norm ?_).2 ?_
    · exact ((hf.continuous_iteratedFDeriv (m := 1) (by exact_mod_cast le_top)).norm.pow 2).aestronglyMeasurable
    · have h4 : Integrable (fun z => ‖Train.jet 1 (Cyl.curl (v r)) z‖ ^ (4:ℝ)) (Cyl.cellμ c) := by
        have h := hgmem.integrable_norm_rpow (by simp) ENNReal.ofReal_ne_top
        rwa [ENNReal.toReal_ofReal (by norm_num : (0:ℝ) ≤ 4)] at h
      refine h4.congr (Filter.Eventually.of_forall fun z => ?_)
      show ‖Train.jet 1 (Cyl.curl (v r)) z‖ ^ (4:ℝ) = ‖‖Train.jet 1 (Cyl.curl (v r)) z‖ ^ 2‖ ^ 2
      rw [Real.norm_of_nonneg (sq_nonneg ‖Train.jet 1 (Cyl.curl (v r)) z‖),
        show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
      ring
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := Cyl.cellμ c) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (f := fun z => ‖iteratedFDeriv ℝ 1 (v r) z‖)
    (g := fun z => ‖Train.jet 1 (Cyl.curl (v r)) z‖ ^ 2)
    (Filter.Eventually.of_forall fun z => norm_nonneg _)
    (Filter.Eventually.of_forall fun z => sq_nonneg _)
    (by rw [ENNReal.ofReal_ofNat]; exact hbmem.norm) (by rw [ENNReal.ofReal_ofNat]; exact hgsq)
  simp only [Real.rpow_two] at hH
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = ∫ z, ‖iteratedFDeriv ℝ 1 (v r) z‖ ^ 2 ∂(Cyl.cellμ c) :=
    ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = ∫ z, ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2
      * ‖iteratedFDeriv ℝ 1 (v r) z‖ ∂(Cyl.cellμ c) := ⟨_, rfl⟩
  have hX' : X ≤ K0 * A := by rw [hXdef]; exact hX
  have hXnn : 0 ≤ X := by
    rw [hXdef]
    exact integral_nonneg fun z => sq_nonneg _
  have hZ' : Z = ∫ z, ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ (4:ℝ) ∂(Cyl.cellμ c) := hZ
  have hZ2 : ∫ z, (‖Train.jet 1 (Cyl.curl (v r)) z‖ ^ 2) ^ 2 ∂(Cyl.cellμ c) = Z := by
    rw [hZ]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show (‖Train.jet 1 (Cyl.curl (v r)) z‖ ^ 2) ^ 2
      = ‖Train.jet 1 (Cyl.curl (v r)) z‖ ^ (4:ℝ)
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    ring
  have hSeq : ∫ z, ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ ^ 2 * ‖iteratedFDeriv ℝ 1 (v r) z‖
      ∂(Cyl.cellμ c)
      = ∫ z, ‖iteratedFDeriv ℝ 1 (v r) z‖ * ‖Train.jet 1 (Cyl.curl (v r)) z‖ ^ 2
      ∂(Cyl.cellμ c) :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)
  have hS : S ≤ X ^ (1/2 : ℝ) * Z ^ (1/2 : ℝ) := by
    have h := hH
    rw [← hXdef, hZ2] at h
    rw [hSdef, hSeq]
    exact h
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact integral_nonneg fun z => by positivity
  have hS2 : S ^ 2 ≤ X * Z := by
    have h1 : S ^ 2 ≤ (X ^ (1/2 : ℝ) * Z ^ (1/2 : ℝ)) ^ 2 := pow_le_pow_left₀ hSnn hS 2
    calc S ^ 2 ≤ (X ^ (1/2 : ℝ) * Z ^ (1/2 : ℝ)) ^ 2 := h1
      _ = X * Z := by rw [mul_pow, apL2s_sq_rpow_half hXnn, apL2s_sq_rpow_half hZnn]
  have hS3 : S ^ 2 ≤ (K0 * Cm ^ 4 * A ^ 3) * vortJet c 2 v r := by
    calc S ^ 2 ≤ X * Z := hS2
      _ ≤ (K0 * A) * (Cm ^ 4 * A ^ 2 * vortJet c 2 v r) :=
          mul_le_mul hX' hZle hZnn (mul_nonneg hK0 hA)
      _ = (K0 * Cm ^ 4 * A ^ 3) * vortJet c 2 v r := by ring
  have htri : triJet1 c v r = 4 * S := by
    rw [hSdef]
    rfl
  rw [htri]
  have key := apL2s_amgm hSnn hY0 (mul_nonneg (mul_nonneg hK0 (pow_nonneg hCm 4))
    (pow_nonneg hA 3)) hν hS3
  have e : 16 * (K0 * Cm ^ 4) * A ^ 3 / ν = 16 * (K0 * Cm ^ 4 * A ^ 3) / ν := by ring
  rw [e]
  exact key

end UnforcedLeray.Short.PartI
