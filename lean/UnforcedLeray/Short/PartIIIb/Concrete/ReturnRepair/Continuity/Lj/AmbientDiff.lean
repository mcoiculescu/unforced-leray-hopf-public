import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Continuity.Lj.NewtonVDiff
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.StreamCut
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Ambient.Scale

/-!
# `μ`-Lipschitz ambient bound for `𝓛` (`sourceLAmbientDiff`, helper of `Continuity/Lj.lean`,
source 4776-4796, 4917-4937, 5701-5704, 5918-5920)

Source of record: `the November 2 reference manuscript` (73 pages).

Combines `newtonV_sub_regionBound` (`Continuity/Lj/NewtonVDiff.lean`), the linearity of
`streamCut ν 1 χy` on fields satisfying `SCZHyp`, the stream-cutoff jet bound `streamCutJet`
(`Ambient/StreamCut.lean`) and exact scaling `Scale.lptScale` (`Ambient/Scale.lean`) to prove
`sourceLAmbientDiff`: for `0 < as` and `LHyp` at `μ, μ'`,
`affTerm as 6 (Lpt c ν ε μ χo χy M - Lpt c ν ε μ' χo χy M) s ≤ C ε³ |μ - μ'| oldN0 c ν M`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- For `Z` satisfying `SCZHyp ν B Z` and `y ∈ psiU ν`, `t ↦ psiF Z t y` is integrable on
`Ioi 1`. -/
theorem integrableOn_psiF_of_scZHyp {ν B : ℝ} {Z : Vec3 → Vec3} (hν : 0 < ν) (hB : 0 ≤ B)
    (hZ : SCZHyp ν B Z) {y : Vec3} (hy : y ∈ psiU ν) :
    IntegrableOn (fun t => psiF Z t y) (Ioi (1 : ℝ)) := by
  obtain ⟨ε, hε, bd, hbd, hb⟩ := scPsiF_dom ν B Z hν hB hZ y hy
  have hbdae : ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))), ‖psiF Z t y‖ ≤ bd t :=
    ParamInt7Aux.ae_Ioi_one_of fun t ht => by
      simpa using hb 0 (Nat.zero_le _) t ht y ⟨hy, mem_ball_self hε⟩
  exact hbd.mono' (ParamInt7Aux.aesm_zero (psiF Z) y
    (scPsiF_meas ν B Z hν hB hZ 0 (Nat.zero_le _) y hy)) hbdae

/-- `streamCut ν 1 χy` preserves differences of fields satisfying `SCZHyp`. -/
theorem streamCut_sub_of_scZHyp {ν B₁ B₂ : ℝ} {Z₁ Z₂ : Vec3 → Vec3} {χy : ℝ → ℝ}
    (hν : 0 < ν) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hZ₁ : SCZHyp ν B₁ Z₁) (hZ₂ : SCZHyp ν B₂ Z₂) (hχy : IsStreamCutoff χy) :
    streamCut ν 1 χy (Z₁ - Z₂) = streamCut ν 1 χy Z₁ - streamCut ν 1 χy Z₂ := by
  funext y
  by_cases hy : y ∈ xjOut ν
  · simp only [Pi.sub_apply]
    rw [xj_stream_zero_on_out hχy _ hy, xj_stream_zero_on_out hχy _ hy,
      xj_stream_zero_on_out hχy _ hy, sub_zero]
  · have hy_ge : ν ≤ y 0 ^ 2 + y 1 ^ 2 := not_lt.1 hy
    have hcyl_sq : ν ≤ cylR y ^ 2 := by rw [xj_cylR_sq]; exact hy_ge
    have heuc : ν * (11 / 12) < eucSq y := by
      have := xj_sq_le_eucSq y
      linarith
    have hcyl_pos : 0 < cylR y := by
      rcases (xj_cylR_nonneg y).eq_or_lt with h0 | hpos
      · exfalso; rw [← h0] at hcyl_sq; nlinarith
      · exact hpos
    have hyU : y ∈ psiU ν := ⟨heuc, hcyl_pos⟩
    have hint1 := integrableOn_psiF_of_scZHyp hν hB₁ hZ₁ hyU
    have hint2 := integrableOn_psiF_of_scZHyp hν hB₂ hZ₂ hyU
    have hpsiF : (fun t => psiF (Z₁ - Z₂) t y) = fun t => psiF Z₁ t y - psiF Z₂ t y := by
      funext t
      simp only [psiF, Pi.sub_apply]
      ring
    have hpsi : streamPsi (Z₁ - Z₂) y = streamPsi Z₁ y - streamPsi Z₂ y := by
      rw [scPsiSubst (Z₁ - Z₂) y hcyl_pos, scPsiSubst Z₁ y hcyl_pos, scPsiSubst Z₂ y hcyl_pos,
        hpsiF, integral_sub hint1 hint2]
      ring
    simp only [streamCut, Pi.sub_apply, hpsi, smul_sub, mul_sub, sub_smul]
    abel

/-- `SCZHyp` for `newtonV c ν μ χo M - newtonV c ν (μ + 1) χo M`. -/
theorem scZHyp_newtonV_diff {c ν μ : ℝ} {χo : ℝ → ℝ} (hc : 0 < c) (hν : 0 < ν)
    (hχo : IsOutwardCutoff χo) (hμ : 0 ≤ μ) {M : Chart → Mat3} (hM : OldThinFinite c ν M) :
    ∃ B : ℝ, 0 ≤ B ∧
      SCZHyp ν B (newtonV c ν μ χo M - newtonV c ν (μ + 1) χo M) := by
  obtain ⟨C, hC⟩ := newtonVRegionBound χo
  have hN0 := oldN0_nonneg c ν hν M
  have hmu1 : 0 ≤ μ + 1 := by linarith
  obtain ⟨h1, h1b⟩ := hC c ν μ hc hν hχo hμ M hM
  obtain ⟨h2, h2b⟩ := hC c ν (μ + 1) hc hν hχo hmu1 M hM
  set S : ℝ := ∑ m ∈ Finset.range 8, (|C m| + |C m|) with hSdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨S * oldN0 c ν M, mul_nonneg hSnn hN0, h1.sub h2, ?_⟩
  intro m hm w hw
  have hopen : IsOpen {w : Vec3 | ν * (11 / 12) < eucSq w} := by
    unfold eucSq; exact isOpen_lt continuous_const (by fun_prop)
  have hat1 : ContDiffAt ℝ 7 (newtonV c ν μ χo M) w := h1.contDiffAt (hopen.mem_nhds hw)
  have hat2 : ContDiffAt ℝ 7 (newtonV c ν (μ + 1) χo M) w := h2.contDiffAt (hopen.mem_nhds hw)
  have hmle : (m : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hm
  rw [iteratedFDeriv_sub_apply (hat1.of_le hmle) (hat2.of_le hmle)]
  have hp : 0 ≤ (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hb1 := h1b m hm w hw
  have hb2 := h2b m hm w hw
  have hSm : |C m| + |C m| ≤ S :=
    Finset.single_le_sum (f := fun m => |C m| + |C m|) (fun _ _ => by positivity)
      (Finset.mem_range.2 (by omega))
  have hCm : C m + C m ≤ S := le_trans (add_le_add (le_abs_self _) (le_abs_self _)) hSm
  calc ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M) w -
          iteratedFDeriv ℝ m (newtonV c ν (μ + 1) χo M) w‖
      ≤ ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M) w‖ +
          ‖iteratedFDeriv ℝ m (newtonV c ν (μ + 1) χo M) w‖ := norm_sub_le _ _
    _ ≤ C m * oldN0 c ν M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) +
          C m * oldN0 c ν M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := add_le_add hb1 hb2
    _ = (C m + C m) * (oldN0 c ν M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) := by ring
    _ ≤ S * (oldN0 c ν M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) :=
        mul_le_mul_of_nonneg_right hCm (mul_nonneg hN0 hp)
    _ = (S * oldN0 c ν M) * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by ring

/-- The `ε = 1` jet bound for the difference `Lpt c ν 1 μ χo χy M - Lpt c ν 1 μ' χo χy M`. -/
theorem jetEps1_sub (χo χy : ℝ → ℝ) :
    ∃ C : ℝ, ∀ (c ν μ μ' : ℝ), LHyp c ν 1 μ χo χy → LHyp c ν 1 μ' χo χy →
      ∀ M : Chart → Mat3, OldThinFinite c ν M → ∀ s : ℝ, 0 < s → ∀ j : ℕ, j ≤ 6 →
        frob (sDerivIter j (Lpt c ν 1 μ χo χy M - Lpt c ν 1 μ' χo χy M) s) ≤
          C * |μ - μ'| * s ^ (5 / 2 : ℝ) * oldN0 c ν M := by
  obtain ⟨C, hC0, hC⟩ := newtonV_sub_regionBound χo
  obtain ⟨C0, hC0_jet⟩ := streamCutJet χy
  obtain ⟨C4, hC4⟩ := scXJet_of_parts χy scPsiSmooth scPsiBound (scChiJet χy)
  set S : ℝ := ∑ m ∈ Finset.range 8, (C m + C m) with hSdef
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun m _ => add_nonneg (hC0 m) (hC0 m)
  refine ⟨C0 * S, ?_⟩
  intro c ν μ μ' h h' M hM s hs j hj
  have hN0 := oldN0_nonneg c ν h.nu_pos M
  have hmu0 : 0 ≤ μ := h.mu_pos.le
  have hmu'0 : 0 ≤ μ' := h'.mu_pos.le
  have hmu1 : 0 ≤ μ + 1 := by linarith
  have hmu'1 : 0 ≤ μ' + 1 := by linarith
  obtain ⟨h1, h1b⟩ := hC c ν μ μ' h.c_pos h.nu_pos h.chiO hmu0 hmu'0 M hM
  obtain ⟨h2, h2b⟩ := hC c ν (μ + 1) (μ' + 1) h.c_pos h.nu_pos h.chiO hmu1 hmu'1 M hM
  have habs1 : |(μ + 1) - (μ' + 1)| = |μ - μ'| := by ring_nf
  set Z₁ : Vec3 → Vec3 := newtonV c ν μ χo M - newtonV c ν (μ + 1) χo M with hZ₁
  set Z₂ : Vec3 → Vec3 := newtonV c ν μ' χo M - newtonV c ν (μ' + 1) χo M with hZ₂
  set Z : Vec3 → Vec3 := Z₁ - Z₂ with hZ
  have hZ_eq : Z = (newtonV c ν μ χo M - newtonV c ν μ' χo M) -
      (newtonV c ν (μ + 1) χo M - newtonV c ν (μ' + 1) χo M) := by
    funext w; simp only [hZ, hZ₁, hZ₂, Pi.sub_apply]; abel
  have hopen : IsOpen {w : Vec3 | ν * (11 / 12) < eucSq w} := by
    unfold eucSq; exact isOpen_lt continuous_const (by fun_prop)
  have hZs : ContDiffOn ℝ 7 Z {w | ν * (11 / 12) < eucSq w} := by
    rw [hZ_eq]; exact h1.sub h2
  have hZb : ∀ m : ℕ, m ≤ 7 → ∀ w : Vec3, ν * (11 / 12) < eucSq w →
      ‖iteratedFDeriv ℝ m Z w‖ ≤
        (S * |μ - μ'| * oldN0 c ν M) * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by
    intro m hm w hw
    have hat1 : ContDiffAt ℝ 7 (newtonV c ν μ χo M - newtonV c ν μ' χo M) w :=
      h1.contDiffAt (hopen.mem_nhds hw)
    have hat2 : ContDiffAt ℝ 7 (newtonV c ν (μ + 1) χo M - newtonV c ν (μ' + 1) χo M) w :=
      h2.contDiffAt (hopen.mem_nhds hw)
    have hmle : (m : WithTop ℕ∞) ≤ 7 := by exact_mod_cast hm
    rw [hZ_eq, iteratedFDeriv_sub_apply (hat1.of_le hmle) (hat2.of_le hmle)]
    have hp : 0 ≤ (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) :=
      Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hb1 := h1b m hm w hw
    have hb2 := h2b m hm w hw
    rw [habs1] at hb2
    have hSm : C m + C m ≤ S :=
      Finset.single_le_sum (f := fun m => C m + C m)
        (fun k _ => add_nonneg (hC0 k) (hC0 k)) (Finset.mem_range.2 (by omega))
    calc ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M - newtonV c ν μ' χo M) w -
            iteratedFDeriv ℝ m (newtonV c ν (μ + 1) χo M - newtonV c ν (μ' + 1) χo M) w‖
        ≤ ‖iteratedFDeriv ℝ m (newtonV c ν μ χo M - newtonV c ν μ' χo M) w‖ +
            ‖iteratedFDeriv ℝ m (newtonV c ν (μ + 1) χo M - newtonV c ν (μ' + 1) χo M) w‖ :=
          norm_sub_le _ _
      _ ≤ C m * |μ - μ'| * oldN0 c ν M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) +
            C m * |μ - μ'| * oldN0 c ν M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) :=
          add_le_add hb1 hb2
      _ = (C m + C m) * (|μ - μ'| * oldN0 c ν M *
            (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) := by ring
      _ ≤ S * (|μ - μ'| * oldN0 c ν M * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m)) :=
          mul_le_mul_of_nonneg_right hSm (mul_nonneg (mul_nonneg (abs_nonneg _) hN0) hp)
      _ = (S * |μ - μ'| * oldN0 c ν M) * (Real.sqrt (eucSq w)) ^ (-(4 : ℝ) - m) := by ring
  obtain ⟨B₁, hB₁, hZ₁_hyp⟩ := scZHyp_newtonV_diff h.c_pos h.nu_pos h.chiO hmu0 hM
  obtain ⟨B₂, hB₂, hZ₂_hyp⟩ := scZHyp_newtonV_diff h.c_pos h.nu_pos h.chiO hmu'0 hM
  have hsc_sub : streamCut ν 1 χy Z = streamCut ν 1 χy Z₁ - streamCut ν 1 χy Z₂ :=
    streamCut_sub_of_scZHyp h.nu_pos hB₁ hB₂ hZ₁_hyp hZ₂_hyp h.chiY
  have hY : ∀ μ'' : ℝ, youngW c ν 1 μ'' χo M = newtonV c ν μ'' χo M := by
    intro μ''; funext y; simp [youngW]
  have hL : Lpt c ν 1 μ χo χy M - Lpt c ν 1 μ' χo χy M = fun s' : ℝ => if 0 < s' then
        (fun i k => fderiv ℝ (streamCut ν 1 χy Z) ![(1 : ℝ)⁻¹ / Real.sqrt s', 0, 0]
          (Pi.single k 1) i)
        else (0 : Mat3) := by
    funext s'
    simp only [Pi.sub_apply, Lpt, Xmt, hY, ← hZ₁, ← hZ₂]
    split_ifs with hs'
    · have hpos_cyl : 0 < cylR ![(1 : ℝ)⁻¹ / Real.sqrt s', 0, 0] := by
        have h1 : (0 : ℝ) < (1 : ℝ)⁻¹ / Real.sqrt s' := div_pos (by norm_num) (Real.sqrt_pos.2 hs')
        unfold cylR
        exact Real.sqrt_pos.2 (by simp; positivity)
      have hd1 : DifferentiableAt ℝ (streamCut ν 1 χy Z₁) ![(1 : ℝ)⁻¹ / Real.sqrt s', 0, 0] :=
        (((hC4 ν B₁ h.nu_pos hB₁ Z₁ hZ₁_hyp h.chiY _ hpos_cyl).1).of_le
          (by norm_num : (1 : WithTop ℕ∞) ≤ 7)).differentiableAt one_ne_zero
      have hd2 : DifferentiableAt ℝ (streamCut ν 1 χy Z₂) ![(1 : ℝ)⁻¹ / Real.sqrt s', 0, 0] :=
        (((hC4 ν B₂ h.nu_pos hB₂ Z₂ hZ₂_hyp h.chiY _ hpos_cyl).1).of_le
          (by norm_num : (1 : WithTop ℕ∞) ≤ 7)).differentiableAt one_ne_zero
      rw [hsc_sub, fderiv_sub hd1 hd2]
      rfl
    · simp
  rw [hL]
  have hBnn : 0 ≤ S * |μ - μ'| * oldN0 c ν M := by positivity
  have := hC0_jet ν (S * |μ - μ'| * oldN0 c ν M) h.nu_pos hBnn Z hZs hZb h.chiY s hs j hj
  calc _ ≤ C0 * (S * |μ - μ'| * oldN0 c ν M) * s ^ (5 / 2 : ℝ) := this
    _ = C0 * S * |μ - μ'| * s ^ (5 / 2 : ℝ) * oldN0 c ν M := by ring

/-- **`sourceLAmbientDiff`** (source 4776-4796, 4917-4937, 5701-5704, 5918-5920): the `μ`-Lipschitz
ambient bound for `Lpt`. -/
theorem sourceLAmbientDiff (as : ℝ) (χo χy : ℝ → ℝ) (has : 0 < as) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c ν ε μ μ' : ℝ), LHyp c ν ε μ χo χy → LHyp c ν ε μ' χo χy →
      ∀ M : Chart → Mat3, OldThinFinite c ν M →
        ∀ s, 0 < s →
          affTerm as 6 (Lpt c ν ε μ χo χy M - Lpt c ν ε μ' χo χy M) s ≤
            C * ε ^ 3 * |μ - μ'| * oldN0 c ν M := by
  obtain ⟨C, hC⟩ := jetEps1_sub χo χy
  refine ⟨7 * |C|, by positivity, ?_⟩
  intro c ν ε μ μ' h h' M hM s hs
  have hε := h.eps_pos
  have hN0 := oldN0_nonneg c ν h.nu_pos M
  have hL : Lpt c ν ε μ χo χy M - Lpt c ν ε μ' χo χy M =
      ε ^ 3 • (Lpt c ν 1 μ χo χy M - Lpt c ν 1 μ' χo χy M) := by
    funext s'
    simp only [Pi.sub_apply, Pi.smul_apply,
      Scale.lptScale c ν ε μ χo χy M hε s', Scale.lptScale c ν ε μ' χo χy M hε s', smul_sub]
  set D1 : ℝ → Mat3 := Lpt c ν 1 μ χo χy M - Lpt c ν 1 μ' χo χy M
  have hit : ∀ j : ℕ, sDerivIter j (ε ^ 3 • D1) = ε ^ 3 • sDerivIter j D1 := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      funext t
      simp only [sDerivIter, sDeriv, ih]
      rw [show (ε ^ 3 • sDerivIter j D1) = fun t => ε ^ 3 • sDerivIter j D1 t from rfl,
        deriv_fun_const_smul_field (ε ^ 3)]
      simp only [Pi.smul_apply]
      exact smul_comm _ _ _
  have hj : ∀ j ∈ Finset.range 7, frob (sDerivIter j (Lpt c ν ε μ χo χy M - Lpt c ν ε μ' χo χy M) s) ≤
      ε ^ 3 * (|C| * |μ - μ'| * s ^ (5 / 2 : ℝ) * oldN0 c ν M) := by
    intro j hj'
    rw [hL, hit j]
    have h1 := hC c ν μ μ'
      (LHyp.mk h.c_pos h.nu_pos h.nu_le one_pos h.mu_pos h.mu_lt h.chiO h.chiY)
      (LHyp.mk h'.c_pos h'.nu_pos h'.nu_le one_pos h'.mu_pos h'.mu_lt h'.chiO h'.chiY)
      M hM s hs j (by simpa [Nat.lt_succ_iff] using hj')
    have hfs : frob (ε ^ 3 • sDerivIter j D1 s) = ε ^ 3 * frob (sDerivIter j D1 s) := by
      unfold frob
      have : ∀ i k, (ε ^ 3 • sDerivIter j D1 s) i k ^ 2 =
          (ε ^ 3) ^ 2 * (sDerivIter j D1 s i k) ^ 2 := by
        intro i k; simp [mul_pow]
      simp only [this, ← Finset.mul_sum]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    show frob (ε ^ 3 • sDerivIter j D1 s) ≤ _
    rw [hfs]
    have hpos : 0 ≤ ε ^ 3 := by positivity
    have hleC : C * |μ - μ'| * s ^ (5 / 2 : ℝ) * oldN0 c ν M ≤
        |C| * |μ - μ'| * s ^ (5 / 2 : ℝ) * oldN0 c ν M :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _))
          (Real.rpow_nonneg hs.le _)) hN0
    exact mul_le_mul_of_nonneg_left (le_trans h1 hleC) hpos
  unfold affTerm affSum
  have hsum := Finset.sum_le_sum hj
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hex : Real.exp (-as * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hsm : s ^ (-(5 / 2 : ℝ)) * s ^ (5 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hs]; simp
  have hs0 : 0 ≤ s ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hs.le _
  have hnn : 0 ≤ ∑ j ∈ Finset.range (6 + 1),
      frob (sDerivIter j (Lpt c ν ε μ χo χy M - Lpt c ν ε μ' χo χy M) s) :=
    Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _
  calc Real.exp (-as * s) * s ^ (-(5 / 2 : ℝ)) *
        ∑ j ∈ Finset.range (6 + 1),
          frob (sDerivIter j (Lpt c ν ε μ χo χy M - Lpt c ν ε μ' χo χy M) s)
      ≤ 1 * s ^ (-(5 / 2 : ℝ)) *
        ∑ j ∈ Finset.range (6 + 1),
          frob (sDerivIter j (Lpt c ν ε μ χo χy M - Lpt c ν ε μ' χo χy M) s) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hex hs0) hnn
    _ ≤ 1 * s ^ (-(5 / 2 : ℝ)) *
        ((7 : ℕ) * (ε ^ 3 * (|C| * |μ - μ'| * s ^ (5 / 2 : ℝ) * oldN0 c ν M))) :=
        mul_le_mul_of_nonneg_left (by simpa using hsum) (by positivity)
    _ = 7 * |C| * ε ^ 3 * |μ - μ'| * oldN0 c ν M *
        (s ^ (-(5 / 2 : ℝ)) * s ^ (5 / 2 : ℝ)) := by push_cast; ring
    _ = 7 * |C| * ε ^ 3 * |μ - μ'| * oldN0 c ν M := by rw [hsm, mul_one]

end UnforcedLeray.Short.PartIIIb.Concrete
