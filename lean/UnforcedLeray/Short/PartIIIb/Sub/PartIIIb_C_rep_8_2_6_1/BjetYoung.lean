import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_8_2_6_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Levels
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AsymNuEps
import UnforcedLeray.Short.PartIIIb.Concrete.AffineEnvelope

/-!
# `PartIII-b:C/rep/8/2/6/1/1`: Lemma 1 `BjetYoung` from `ActualJet` and `JetClock`

Source `the November 2 reference manuscript` 5400-5413 (actual jet), 5446,
5449-5458 (`B_T = B_j + clock`).  On the young range `s ≤ 1/ν`, `A^y = A` near `s` (and at `s = 1/ν`
through `χ_f'(1) = 0`), so `B = s⁻¹ (s∂_s A) + (μ/s) A`, and the bound follows from the
`(s∂_s)^j A` bounds of `ActualJetAt` and the clock bound of `JetClockAt`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

theorem bjY_frob_sub_le (A B : Mat3) : frob (A - B) ≤ frob A + frob B := by
  have e : A - B = A + (-1 : ℝ) • B := by rw [neg_one_smul, sub_eq_add_neg]
  have h2 : frob ((-1 : ℝ) • B) = frob B := by
    rw [frob_smul]; simp
  rw [e]
  linarith [frob_add_le A ((-1 : ℝ) • B)]

theorem bjY_frob_D (s μ : ℝ) (hs : 0 < s) (hμ : |μ| ≤ 1) (X Y : Mat3) :
    frob (s⁻¹ • X + (μ / s) • Y) ≤ s⁻¹ * frob X + s⁻¹ * frob Y := by
  have h1 := frob_add_le (s⁻¹ • X) ((μ / s) • Y)
  have h2 : frob (s⁻¹ • X) = s⁻¹ * frob X := by
    rw [frob_smul, abs_of_pos (inv_pos.2 hs)]
  have h3 : frob ((μ / s) • Y) ≤ s⁻¹ * frob Y := by
    rw [frob_smul]
    have hm : |μ / s| ≤ s⁻¹ := by
      rw [abs_div, abs_of_pos hs, div_eq_mul_inv]
      calc |μ| * s⁻¹ ≤ 1 * s⁻¹ := mul_le_mul_of_nonneg_right hμ (inv_nonneg.2 hs.le)
        _ = s⁻¹ := one_mul _
    exact mul_le_mul_of_nonneg_right hm (frob_nonneg _)
  linarith

/-- The derivative of `χ(ν·)A` at `s ≤ 1/ν` is that of `A`. -/
theorem bjY_deriv_Ay {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) {ν : ℝ} (hν : 0 < ν)
    (A : ℝ → Mat3) {s : ℝ} (hνs : ν * s ≤ 1) :
    deriv (Ay ν χ A) s = deriv A s := by
  rcases lt_or_eq_of_le hνs with hlt | heq
  · apply Filter.EventuallyEq.deriv_eq
    have hcont : Continuous (fun t : ℝ => ν * t) := continuous_const.mul continuous_id
    have hopen : ∀ᶠ t in 𝓝 s, ν * t < 1 :=
      (hcont.tendsto s).eventually (gt_mem_nhds hlt)
    filter_upwards [hopen] with t ht
    simp only [Ay]
    rw [hχ.one (ν * t) ht.le, one_smul]
  · have hχd : DifferentiableAt ℝ χ (ν * s) := hχ.smooth.differentiable (by simp) _
    have hd0 : deriv χ (ν * s) = 0 := by
      rw [heq]
      have hloc : IsLocalMax χ 1 := by
        unfold IsLocalMax IsMaxFilter
        exact Filter.Eventually.of_forall (fun t => by
          show χ t ≤ χ 1
          rw [hχ.one 1 le_rfl]
          exact (hχ.range t).2)
      exact hloc.deriv_eq_zero
    have hlin : HasDerivAt (fun t : ℝ => ν * t) ν s := by
      simpa using (hasDerivAt_id s).const_mul ν
    have hg : HasDerivAt (fun t : ℝ => χ (ν * t)) 0 s := by
      have := hχd.hasDerivAt.comp s hlin
      rw [hd0, zero_mul] at this
      exact this
    have h1 : χ (ν * s) = 1 := hχ.one _ heq.le
    by_cases hA : DifferentiableAt ℝ A s
    · have hY : HasDerivAt (Ay ν χ A) (χ (ν * s) • deriv A s + (0 : ℝ) • A s) s :=
        hg.smul hA.hasDerivAt
      rw [hY.deriv, h1, zero_smul, add_zero, one_smul]
    · have hne : χ (ν * s) ≠ 0 := by rw [h1]; norm_num
      have hnd : ¬ DifferentiableAt ℝ (Ay ν χ A) s := by
        intro hY
        apply hA
        have hinv : DifferentiableAt ℝ (fun t : ℝ => (χ (ν * t))⁻¹) s :=
          hg.differentiableAt.inv hne
        have hprod := hinv.smul hY
        refine hprod.congr_of_eventuallyEq ?_
        have hne' : ∀ᶠ t in 𝓝 s, χ (ν * t) ≠ 0 := hg.continuousAt.eventually_ne hne
        filter_upwards [hne'] with t ht
        show A t = (χ (ν * t))⁻¹ • (χ (ν * t) • A t)
        rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [deriv_zero_of_not_differentiableAt hnd, deriv_zero_of_not_differentiableAt hA]

/-- The young-range identity `B = s⁻¹ (s∂_s A) + (μ/s) A`. -/
theorem bjY_Bmat_eq {χ : ℝ → ℝ} (hχ : IsSourceCutoffC χ) {ν : ℝ} (hν : 0 < ν)
    (μ : ℝ) (A : ℝ → Mat3) {s : ℝ} (hs : 0 < s) (hνs : ν * s ≤ 1) :
    Bmat ν μ χ A s = s⁻¹ • sDerivIter 1 A s + (μ / s) • A s := by
  have hAy : Ay ν χ A s = A s := by
    simp only [Ay, hχ.one (ν * s) hνs, one_smul]
  show deriv (Ay ν χ A) s + (μ / s) • Ay ν χ A s = s⁻¹ • sDerivIter 1 A s + (μ / s) • A s
  rw [bjY_deriv_Ay hχ hν A hνs, hAy]
  show deriv A s + (μ / s) • A s = s⁻¹ • (s • deriv A s) + (μ / s) • A s
  rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

theorem bjY_key {x b a : ℝ} {N : ℝ≥0∞} (hb : 0 ≤ b)
    (h : ENNReal.ofReal x ≤ ENNReal.ofReal a * N) :
    ENNReal.ofReal (b * x) ≤ ENNReal.ofReal (b * a) * N := by
  rw [ENNReal.ofReal_mul hb, ENNReal.ofReal_mul hb, mul_assoc]
  gcongr

theorem bjY_mulN {p q : ℝ≥0∞} {N : ℝ≥0∞} (h : p ≤ q) : p * N ≤ q * N := by
  gcongr

theorem bjY_mono {x u v : ℝ} {N : ℝ≥0∞} (huv : u ≤ v)
    (h : ENNReal.ofReal x ≤ ENNReal.ofReal u * N) :
    ENNReal.ofReal x ≤ ENNReal.ofReal v * N :=
  h.trans (bjY_mulN (ENNReal.ofReal_le_ofReal huv))

theorem bjY_add3 {x y z a b c : ℝ} {N : ℝ≥0∞} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h1 : ENNReal.ofReal x ≤ ENNReal.ofReal a * N) (h2 : ENNReal.ofReal y ≤ ENNReal.ofReal b * N)
    (h3 : ENNReal.ofReal z ≤ ENNReal.ofReal c * N) :
    ENNReal.ofReal (x + y + z) ≤ ENNReal.ofReal (a + b + c) * N := by
  rw [ENNReal.ofReal_add (add_nonneg hx hy) hz, ENNReal.ofReal_add hx hy,
    ENNReal.ofReal_add (add_nonneg ha hb) hc, ENNReal.ofReal_add ha hb, add_mul, add_mul]
  exact add_le_add (add_le_add h1 h2) h3

theorem bjY_s52 {s : ℝ} (hs : 0 < s) : s ^ (5 / 2 : ℝ) = s ^ (3 / 2 : ℝ) * s := by
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hs, Real.rpow_one]

theorem bjY_inv_mul_s52 {s C X : ℝ} (hs : 0 < s) :
    s⁻¹ * (C * X * s ^ (5 / 2 : ℝ)) = C * X * s ^ (3 / 2 : ℝ) := by
  rw [bjY_s52 hs, show s⁻¹ * (C * X * (s ^ (3 / 2 : ℝ) * s))
      = C * X * s ^ (3 / 2 : ℝ) * (s⁻¹ * s) by ring, inv_mul_cancel₀ hs.ne', mul_one]

theorem bjY_pow_le {ν : ℝ} (hν : 0 < ν) (hν1 : ν ≤ 1) {k k' : ℕ} (hk : k ≤ k') :
    ν⁻¹ ^ k ≤ ν⁻¹ ^ k' :=
  pow_le_pow_right₀ ((one_le_inv₀ hν).2 hν1) hk

theorem bjY_pieceA {ν ε s C x : ℝ} {N : ℝ≥0∞} {kA kB : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hε : 0 ≤ ε) (hs : 0 < s)
    (h : ENNReal.ofReal x ≤ ENNReal.ofReal (C * ν⁻¹ ^ kA * ε ^ 3 * s ^ (5 / 2 : ℝ)) * N) :
    ENNReal.ofReal (s⁻¹ * x) ≤
      ENNReal.ofReal (|C| * (ν⁻¹ ^ (kA + kB) * ε ^ 3 * s ^ (3 / 2 : ℝ))) * N := by
  refine (bjY_key (inv_nonneg.2 hs.le) h).trans (bjY_mulN (ENNReal.ofReal_le_ofReal ?_))
  rw [bjY_inv_mul_s52 hs]
  have hw : 0 ≤ ε ^ 3 * s ^ (3 / 2 : ℝ) := mul_nonneg (pow_nonneg hε 3) (Real.rpow_nonneg hs.le _)
  have h1 : C * ν⁻¹ ^ kA ≤ |C| * ν⁻¹ ^ (kA + kB) :=
    mul_le_mul (le_abs_self C) (bjY_pow_le hν hν1 (Nat.le_add_right kA kB))
      (pow_nonneg (inv_nonneg.2 hν.le) _) (abs_nonneg C)
  calc C * ν⁻¹ ^ kA * ε ^ 3 * s ^ (3 / 2 : ℝ)
      = (C * ν⁻¹ ^ kA) * (ε ^ 3 * s ^ (3 / 2 : ℝ)) := by ring
    _ ≤ (|C| * ν⁻¹ ^ (kA + kB)) * (ε ^ 3 * s ^ (3 / 2 : ℝ)) := mul_le_mul_of_nonneg_right h1 hw
    _ = |C| * (ν⁻¹ ^ (kA + kB) * ε ^ 3 * s ^ (3 / 2 : ℝ)) := by ring

theorem bjY_pieceB {ν ε s C q : ℝ} {N : ℝ≥0∞} {kA kB : ℕ} (hν : 0 < ν) (hν1 : ν ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hs : 0 < s) (hνs : ν * s ≤ 1)
    (h : ENNReal.ofReal q ≤ ENNReal.ofReal (C * ν⁻¹ ^ kB * ν * ε ^ 5 * s ^ (5 / 2 : ℝ)) * N) :
    ENNReal.ofReal q ≤
      ENNReal.ofReal (|C| * (ν⁻¹ ^ (kA + kB) * ε ^ 3 * s ^ (3 / 2 : ℝ))) * N := by
  refine h.trans (bjY_mulN (ENNReal.ofReal_le_ofReal ?_))
  have hw : 0 ≤ ε ^ 3 * s ^ (3 / 2 : ℝ) := mul_nonneg (pow_nonneg hε 3) (Real.rpow_nonneg hs.le _)
  have hq1 : ν * s * ε ^ 2 ≤ 1 := mul_le_one₀ hνs (sq_nonneg ε) (pow_le_one₀ hε hε1)
  have h2 : ν * ε ^ 5 * s ^ (5 / 2 : ℝ) ≤ ε ^ 3 * s ^ (3 / 2 : ℝ) := by
    rw [bjY_s52 hs]
    calc ν * ε ^ 5 * (s ^ (3 / 2 : ℝ) * s) = (ε ^ 3 * s ^ (3 / 2 : ℝ)) * (ν * s * ε ^ 2) := by ring
      _ ≤ (ε ^ 3 * s ^ (3 / 2 : ℝ)) * 1 := mul_le_mul_of_nonneg_left hq1 hw
      _ = ε ^ 3 * s ^ (3 / 2 : ℝ) := mul_one _
  have h1 : C * ν⁻¹ ^ kB ≤ |C| * ν⁻¹ ^ (kA + kB) :=
    mul_le_mul (le_abs_self C) (bjY_pow_le hν hν1 (Nat.le_add_left kB kA))
      (pow_nonneg (inv_nonneg.2 hν.le) _) (abs_nonneg C)
  have hz : 0 ≤ ν * ε ^ 5 * s ^ (5 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg hν.le (pow_nonneg hε 5)) (Real.rpow_nonneg hs.le _)
  calc C * ν⁻¹ ^ kB * ν * ε ^ 5 * s ^ (5 / 2 : ℝ)
      = (C * ν⁻¹ ^ kB) * (ν * ε ^ 5 * s ^ (5 / 2 : ℝ)) := by ring
    _ ≤ (|C| * ν⁻¹ ^ (kA + kB)) * (ε ^ 3 * s ^ (3 / 2 : ℝ)) :=
        mul_le_mul h1 h2 hz (mul_nonneg (abs_nonneg C) (pow_nonneg (inv_nonneg.2 hν.le) _))
    _ = |C| * (ν⁻¹ ^ (kA + kB) * ε ^ 3 * s ^ (3 / 2 : ℝ)) := by ring

/-- **Lemma 1 at one regime** (source 5400-5413, 5446, 5449-5458): on the young range the
`BjetYoungBoundAt` bound with constants `2|C_A| + |C_J|` and `k_A + k_J`, given `|μ| ≤ 1`,
`ν, ε ≤ 1` and the source cutoff `χ_f`. -/
theorem bjY_pointwise (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ CA CJ : ℝ)
    (kA kJ : ℕ) (hχ : IsSourceCutoffC K.χf) (hμ : |μ| ≤ 1) (hν1 : L.ν ≤ 1) (hε1 : L.ε ≤ 1)
    (hA : ActualJetAt Pl K L μ CA kA) (hJ : JetClockAt Pl K L μ CJ kJ) :
    BjetYoungBoundAt Pl K L μ (2 * |CA| + |CJ|) (kA + kJ) := by
  intro T s hs hsν
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hνs : L.ν * s ≤ 1 := by
    rw [mul_comm]; exact (le_div_iff₀ hν).1 hsν
  obtain ⟨hAj, -⟩ := hA T
  obtain ⟨hJ1, hJ2⟩ := hJ T s ⟨hs, hsν⟩
  have h1 := hAj 1 (by norm_num) s hs
  have h0 : ENNReal.ofReal (frob (LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T s))
      ≤ ENNReal.ofReal (CA * L.ν⁻¹ ^ kA * L.ε ^ 3 * s ^ (5 / 2 : ℝ)) * oldN1 Pl K L T :=
    hAj 0 (by norm_num) s hs
  set A := LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T with hAdef
  set Bm := Bmat L.ν μ K.χf A s with hBmdef
  set Bj := Bjet (cOf L.ν) L.ν L.ε μ K.χo K.χy (thinRep T) s with hBjdef
  have hBm : Bm = s⁻¹ • sDerivIter 1 A s + (μ / s) • A s :=
    bjY_Bmat_eq hχ hν μ A hs hνs
  have hfB : frob Bj ≤ frob Bm + frob (Bm - Bj) := by
    have e : Bj = Bm - (Bm - Bj) := (sub_sub_cancel Bm Bj).symm
    calc frob Bj = frob (Bm - (Bm - Bj)) := congrArg frob e
      _ ≤ frob Bm + frob (Bm - Bj) := bjY_frob_sub_le _ _
  have hfBm : frob Bm ≤ s⁻¹ * frob (sDerivIter 1 A s) + s⁻¹ * frob (A s) := by
    rw [hBm]; exact bjY_frob_D s μ hs hμ _ _
  have hP : 0 ≤ L.ν⁻¹ ^ (kA + kJ) * L.ε ^ 3 * s ^ (3 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.2 hν.le) _) (pow_nonneg hε.le _))
      (Real.rpow_nonneg hs.le _)
  have hx : 0 ≤ s⁻¹ * frob (sDerivIter 1 A s) :=
    mul_nonneg (inv_nonneg.2 hs.le) (frob_nonneg _)
  have hy : 0 ≤ s⁻¹ * frob (A s) := mul_nonneg (inv_nonneg.2 hs.le) (frob_nonneg _)
  have hz : 0 ≤ frob (Bm - Bj) := frob_nonneg _
  have hsum := bjY_add3 hx hy hz
    (mul_nonneg (abs_nonneg CA) hP) (mul_nonneg (abs_nonneg CA) hP)
    (mul_nonneg (abs_nonneg CJ) hP)
    (bjY_pieceA (kB := kJ) hν hν1 hε.le hs h1)
    (bjY_pieceA (kB := kJ) hν hν1 hε.le hs h0)
    (bjY_pieceB (kA := kA) hν hν1 hε.le hε1 hs hνs hJ2)
  have hreal : frob Bj ≤ s⁻¹ * frob (sDerivIter 1 A s) + s⁻¹ * frob (A s) + frob (Bm - Bj) := by
    linarith
  have htot := (ENNReal.ofReal_le_ofReal hreal).trans hsum
  have hc : |CA| * (L.ν⁻¹ ^ (kA + kJ) * L.ε ^ 3 * s ^ (3 / 2 : ℝ)) +
      |CA| * (L.ν⁻¹ ^ (kA + kJ) * L.ε ^ 3 * s ^ (3 / 2 : ℝ)) +
      |CJ| * (L.ν⁻¹ ^ (kA + kJ) * L.ε ^ 3 * s ^ (3 / 2 : ℝ)) =
      (2 * |CA| + |CJ|) * L.ν⁻¹ ^ (kA + kJ) * L.ε ^ 3 * s ^ (3 / 2 : ℝ) := by ring
  rw [hc] at htot
  exact htot

theorem bjetYoung_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) (h6 : D.ActualJet)
    (h7 : D.JetClock) : D.BjetYoung := by
  obtain ⟨CA, kA, eA⟩ := h6
  obtain ⟨CJ, kJ, eJ⟩ := h7
  refine ⟨2 * |CA| + |CJ|, kA + kJ, ?_⟩
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  have hmu := SeqData.eventually_mu_mem_Ioo D hst.omega_ne hst.sigma_pos hst.sigma_lt
  filter_upwards [eA, eJ, hle, hmu] with n a b hl hm z hz
  obtain ⟨h1, h2⟩ := hm z hz
  exact bjY_pointwise D.Pl D.K (D.level n) (D.mu n z) CA CJ kA kJ hst.chiF
    (abs_le.2 ⟨by linarith, by linarith⟩) hl.1 hl.2 (a z hz) (b z hz)

end UnforcedLeray.Short.PartIIIb.Concrete
