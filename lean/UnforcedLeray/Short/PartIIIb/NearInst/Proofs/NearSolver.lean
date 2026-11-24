import UnforcedLeray.Short.PartIIIb.NearInst.Targets
import UnforcedLeray.Short.PartIIIb.NearProofs
import UnforcedLeray.Short.PartIIIb.Proofs.NearParam
import UnforcedLeray.Short.PartIIIb.Proofs.EpsPow

/-!
# Proof of `nearSolverC_of` (target `NearSolverC`; source 3943-3951, 4109-4124, 4023-4031)

Assembly of the near solver under the parameter choice:

* `NearFlatBoundC` (`hF`) gives `Q = C_F ν⁻ᵏᶠ` for `‖G⁻¹D₀⁻¹G‖`;
* `NearDeltaBoundC` (`hD`) with the parameter choice `nearParam epsPow` gives
  `δ_N ≤ C_D ν⁻ᵏᴰ · C_P ν⁻ᵏᴾ e^{-θd₀/(2ν)}`;
* `QδN < 1/2` for small `ν` (`ns_small`), so `nearInverseComparison` applies;
* `ρ_b = rhoB ≤ 1` for small `ν` (`ns_rhoB_le`, uses `m₀ < 3d₋/11` strictly);
* `NearMaskedFreeBoundC` (`hM`) bounds `g⁻¹S_N g`.

Constants are merged with `ν⁻¹ ≥ 1` (`ν ≤ 1`).
-/

set_option autoImplicit false

noncomputable section

open Filter Topology Set

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- Smallness: `A ν⁻ᴺ e^{-T/(2ν)} < ε₀` for all small `ν > 0`. -/
theorem ns_small (T : ℝ) (hT : 0 < T) (A : ℝ) (N : ℕ) (ε₀ : ℝ) (hε : 0 < ε₀) :
    ∃ ν₁ : ℝ, 0 < ν₁ ∧ ∀ ν : ℝ, 0 < ν → ν ≤ ν₁ →
      A * ν⁻¹ ^ N * Real.exp (-T / (2 * ν)) < ε₀ := by
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = T / 2 := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hs_def]; positivity
  have hsN : s ^ N ≠ 0 := pow_ne_zero _ hs.ne'
  have h1 : Tendsto (fun x : ℝ => (s * x) ^ N * Real.exp (-(s * x))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).comp (tendsto_id.const_mul_atTop hs)
  have h2 : Tendsto (fun x : ℝ => x ^ N * Real.exp (-(s * x))) atTop (𝓝 0) := by
    have h3 := h1.const_mul ((s ^ N)⁻¹)
    rw [mul_zero] at h3
    refine h3.congr (fun x => ?_)
    rw [mul_pow]
    field_simp
  have hB : 0 < |A| + 1 := by positivity
  have hB' : |A| + 1 ≠ 0 := hB.ne'
  have hε' : 0 < ε₀ / (|A| + 1) := div_pos hε hB
  have h4 : ∀ᶠ x in atTop, x ^ N * Real.exp (-(s * x)) < ε₀ / (|A| + 1) :=
    h2.eventually (gt_mem_nhds hε')
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 h4
  have hMpos : 0 < max X 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨(max X 1)⁻¹, inv_pos.2 hMpos, ?_⟩
  intro ν hν hνle
  have hMν : max X 1 ≤ ν⁻¹ := (le_inv_comm₀ hν hMpos).1 hνle
  have hx := hX ν⁻¹ (le_trans (le_max_left X 1) hMν)
  have hnn : 0 ≤ ν⁻¹ ^ N * Real.exp (-(s * ν⁻¹)) := by positivity
  have hexp : -T / (2 * ν) = -(s * ν⁻¹) := by rw [hs_def]; ring
  rw [hexp]
  have hlt' : (|A| + 1) * (ν⁻¹ ^ N * Real.exp (-(s * ν⁻¹))) < ε₀ := by
    calc (|A| + 1) * (ν⁻¹ ^ N * Real.exp (-(s * ν⁻¹)))
        < (|A| + 1) * (ε₀ / (|A| + 1)) := mul_lt_mul_of_pos_left hx hB
      _ = ε₀ := by field_simp
  have hA : A * (ν⁻¹ ^ N * Real.exp (-(s * ν⁻¹)))
      ≤ (|A| + 1) * (ν⁻¹ ^ N * Real.exp (-(s * ν⁻¹))) :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self A]) hnn
  have h5 : A * ν⁻¹ ^ N * Real.exp (-(s * ν⁻¹)) = A * (ν⁻¹ ^ N * Real.exp (-(s * ν⁻¹))) := by
    ring
  linarith

/-- Monotonicity of the constant: `x ≤ C t R ⇒ x ≤ c t R` for `C ≤ c`, `R, t ≥ 0`. -/
theorem ns_mono {x C c t R : ℝ} (h : x ≤ C * t * R) (hC : C ≤ c) (hR : 0 ≤ R) (ht : 0 ≤ t) :
    x ≤ c * t * R :=
  h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC ht) hR)

/-- `ρ_b = rhoB` is positive. -/
theorem ns_rhoB_pos (p : Params) (m0 C0 : ℝ) (k0 : ℕ) (hC0 : 0 < C0) :
    0 < UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 := by
  unfold UnforcedLeray.Short.IIb.rhoB
  have h1 := p.ν_pos
  have h2 := p.ε_pos
  positivity

/-- `ρ_b = rhoB ≤ 1` for small `ν` when `m₀ < 3d₋/11`. -/
theorem ns_rhoB_le (m0 C0 dm dp : ℝ) (k0 : ℕ) (hC0 : 0 < C0) (hm0 : m0 < 3 * dm / 11) :
    ∃ ν₂ : ℝ, 0 < ν₂ ∧ ∀ (p : Params) (d : ℝ),
      UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₂ →
        UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 ≤ 1 := by
  obtain ⟨ν₁, hν₁, hsm⟩ :=
    ns_small (2 * (3 * dm / 11 - m0)) (by linarith) C0 k0 1 one_pos
  refine ⟨ν₁, hν₁, ?_⟩
  intro p d hBG hpν
  have hν := p.ν_pos
  have hε : p.ε = Real.exp (-d / p.ν) := hBG.eps_eq
  have hd : dm ≤ d := hBG.dm_le
  unfold UnforcedLeray.Short.IIb.rhoB
  rw [hε, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← inv_pow]
  have hexp_le : m0 / p.ν + -d / p.ν * (3 / 11) ≤ -(2 * (3 * dm / 11 - m0)) / (2 * p.ν) := by
    have h3 : (m0 - d * (3 / 11)) * p.ν⁻¹ ≤ (-(3 * dm / 11 - m0)) * p.ν⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.2 hν.le)
    have e1 : m0 / p.ν + -d / p.ν * (3 / 11) = (m0 - d * (3 / 11)) * p.ν⁻¹ := by ring
    have e2 : -(2 * (3 * dm / 11 - m0)) / (2 * p.ν) = (-(3 * dm / 11 - m0)) * p.ν⁻¹ := by
      ring
    rw [e1, e2]
    exact h3
  have hsm' := hsm p.ν hν hpν
  have hpos : 0 ≤ C0 * p.ν⁻¹ ^ k0 := by positivity
  calc C0 * p.ν⁻¹ ^ k0 * Real.exp (m0 / p.ν) * Real.exp (-d / p.ν * (3 / 11))
      = C0 * p.ν⁻¹ ^ k0 * Real.exp (m0 / p.ν + -d / p.ν * (3 / 11)) := by
        rw [Real.exp_add]; ring
    _ ≤ C0 * p.ν⁻¹ ^ k0 * Real.exp (-(2 * (3 * dm / 11 - m0)) / (2 * p.ν)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hexp_le) hpos
    _ ≤ 1 := hsm'.le

/-- `deltaNRhs` is nonnegative for a positive curvature `ε`. -/
theorem ns_deltaNRhs_nonneg (a b K ηδ m0 Dp ε ν : ℝ) (hε : 0 < ε) :
    0 ≤ deltaNRhs a b K ηδ m0 Dp ε ν := by
  unfold deltaNRhs
  positivity

/-- **The near solver under the parameter choice** (source 3943-3951, 4109-4124, 4023-4031). -/
theorem nearSolverC_of (hF : NearFlatBoundC) (hD : NearDeltaBoundC) (hM : NearMaskedFreeBoundC) :
    NearSolverC := by
  intro P hP Kset hK hKsub mZ hmZ dm dp hdm
  obtain ⟨K, hKall⟩ := hD P hP Kset hK hKsub mZ hmZ dm dp hdm
  refine ⟨K, ?_⟩
  intro a b δ m0 Dp ha hb hb1 hKab hδ hm0 hm0dm hηθ hm0θ hDpθ C0 k0 hC0 c1 c2 rmax hc1 hc12 hrmax Sig hSig
  unfold thetaAB at hηθ hm0θ hDpθ ⊢
  have hγ : 0 < P.eigenvalue.re := hP.eigenpair.re_pos
  obtain ⟨T, hT⟩ : ∃ T : ℝ,
      T = min (min (a / 2) (b / 2)) (min (1 / 100) (3 / 22)) * (P.eigenvalue.re / 3) :=
    ⟨_, rfl⟩
  have hθ : 0 < min (min (a / 2) (b / 2)) (min (1 / 100) (3 / 22)) :=
    lt_min (lt_min (by linarith) (by linarith)) (lt_min (by norm_num) (by norm_num))
  have hTpos : 0 < T := by rw [hT]; exact mul_pos hθ (by positivity)
  have hη : 0 ≤ etaDelta P.eigenvalue.re δ := by
    unfold etaDelta
    apply mul_nonneg hγ.le
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_nonneg (Real.sinh_nonneg_iff.2 (by linarith)) (Real.cosh_pos _).le
  have hDp0 : 0 < Dp := by
    have : 0 < min (min (a / 2) (b / 2)) (min (1 / 100) (3 / 22)) * (P.eigenvalue.re / 3) := by
      rw [← hT]; exact hTpos
    linarith
  obtain ⟨CF, kF, νF, hνF, hF'⟩ := hF P hP Kset hK hKsub mZ hmZ dm dp hdm
  obtain ⟨CM, kM, νM, hνM, hM'⟩ :=
    hM P hP Kset hK hKsub mZ (by linarith) dm dp hdm b δ hb hb1 hδ
  obtain ⟨CD, kD, νD, hνD, hD'⟩ :=
    hKall a b δ m0 Dp ha hb hb1 hδ hm0 hm0dm hDp0 C0 k0 hC0 Sig hSig
  obtain ⟨CP, kP, νP, hνP, hP'⟩ :=
    (nearParam epsPow) a b P.eigenvalue.re (etaDelta P.eigenvalue.re δ) m0 Dp (K : ℝ) c1 c2 rmax
      ha hb hγ hη hm0.le (Nat.cast_nonneg K) hKab hηθ hm0θ hDpθ hc1 hc12 hrmax
  obtain ⟨νR, hνR, hR⟩ := ns_rhoB_le m0 C0 dm dp k0 hC0 hm0dm
  obtain ⟨cF, hcF0, hcF⟩ : ∃ c : ℝ, 0 ≤ c ∧ CF ≤ c :=
    ⟨max CF 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨cD, hcD0, hcD⟩ : ∃ c : ℝ, 0 ≤ c ∧ CD ≤ c :=
    ⟨max CD 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨cP, hcP0, hcP⟩ : ∃ c : ℝ, 0 ≤ c ∧ CP ≤ c :=
    ⟨max CP 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨cM, hcM0, hcM⟩ : ∃ c : ℝ, 0 ≤ c ∧ CM ≤ c :=
    ⟨max CM 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨νQ, hνQ, hQ⟩ :=
    ns_small T hTpos (cF * cD * cP) (kF + kD + kP) (1 / 2) (by norm_num)
  obtain ⟨CC, hCC⟩ : ∃ CC : ℝ, CC = 2 * cF + 2 * (cF ^ 2 * cD * cP) + cM := ⟨_, rfl⟩
  obtain ⟨kT, hkT⟩ : ∃ k : ℕ, k = 2 * kF + kD + kP + kM := ⟨_, rfl⟩
  have hK3 : 0 ≤ cF ^ 2 * cD * cP := by positivity
  have hCC2 : 2 * cF ≤ CC := by rw [hCC]; linarith
  have hCC3 : 2 * (cF ^ 2 * cD * cP) ≤ CC := by rw [hCC]; linarith
  have hCC4 : cM ≤ CC := by rw [hCC]; linarith
  have hCC0 : 0 ≤ CC := by rw [hCC]; linarith
  obtain ⟨NU, hNU⟩ : ∃ NU : ℝ,
      NU = min (min (min νF νD) (min νM νP)) (min (min νR νQ) 1) := ⟨_, rfl⟩
  have hNUpos : 0 < NU := by
    rw [hNU]
    exact lt_min (lt_min (lt_min hνF hνD) (lt_min hνM hνP)) (lt_min (lt_min hνR hνQ) one_pos)
  have hNUF : NU ≤ νF := by
    rw [hNU]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hNUD : NU ≤ νD := by
    rw [hNU]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hNUM : NU ≤ νM := by
    rw [hNU]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hNUP : NU ≤ νP := by
    rw [hNU]; exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hNUR : NU ≤ νR := by
    rw [hNU]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hNUQ : NU ≤ νQ := by
    rw [hNU]; exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hNU1 : NU ≤ 1 := by
    rw [hNU]; exact (min_le_right _ _).trans (min_le_right _ _)
  rw [← hT]
  refine ⟨CC, kT, NU, hNUpos, ?_⟩
  intro p d hBG hpν hSg hmode hform S_in V rb hsplit hSin μ hμ o hact
  have hνpos : 0 < p.ν := p.ν_pos
  have hεpos : 0 < p.ε := p.ε_pos
  have ht1 : 1 ≤ p.ν⁻¹ := by
    rw [le_inv_comm₀ one_pos hνpos, inv_one]
    exact le_trans hpν hNU1
  have ht0 : 0 ≤ p.ν⁻¹ := inv_nonneg.2 hνpos.le
  have hρpos := ns_rhoB_pos p m0 C0 k0 hC0
  have hρ1 : UnforcedLeray.Short.IIb.rhoB p m0 C0 k0 ≤ 1 :=
    hR p d hBG (le_trans hpν hNUR)
  -- flat free inverse
  obtain ⟨hUD0, hQbd0⟩ := hF' p d hBG (le_trans hpν hNUF) _ hρpos hρ1 μ hμ o hact.flat hact.free
  have hQbd := hQbd0.trans (mul_le_mul_of_nonneg_right hcF (pow_nonneg ht0 kF))
  -- masked near operator
  have hSNbd := hM' p d hBG (le_trans hpν hNUM) _ hρpos hρ1 μ hμ o.SN hact.near
  have he : 0 ≤ Real.exp (-T / (2 * p.ν)) := (Real.exp_pos _).le
  have hSN : ‖gainConjS P.eigenvalue.re p.ν_pos o.SN‖
      ≤ CC * p.ν⁻¹ ^ kT * Real.exp (etaDelta P.eigenvalue.re δ / p.ν) := by
    have hpow : p.ν⁻¹ ^ kM ≤ p.ν⁻¹ ^ kT := pow_le_pow_right₀ ht1 (by omega)
    have he2 : 0 ≤ Real.exp (etaDelta P.eigenvalue.re δ / p.ν) := (Real.exp_pos _).le
    have h1 : CM * p.ν⁻¹ ^ kM * Real.exp (etaDelta P.eigenvalue.re δ / p.ν)
        ≤ cM * p.ν⁻¹ ^ kM * Real.exp (etaDelta P.eigenvalue.re δ / p.ν) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcM (pow_nonneg ht0 _)) he2
    have h2 : cM * p.ν⁻¹ ^ kM * Real.exp (etaDelta P.eigenvalue.re δ / p.ν)
        ≤ CC * p.ν⁻¹ ^ kT * Real.exp (etaDelta P.eigenvalue.re δ / p.ν) :=
      mul_le_mul_of_nonneg_right (mul_le_mul hCC4 hpow (pow_nonneg ht0 _) hCC0) he2
    exact hSNbd.trans (h1.trans h2)
  -- the δ_N bound through the parameter choice
  obtain ⟨Cs, hCs, r, hr, hεeq⟩ := hform
  have hDres := hD' p d hBG (le_trans hpν hNUD) hSg hmode S_in V rb hsplit hSin μ hμ o hact
  have hRnn := ns_deltaNRhs_nonneg a b (K : ℝ) (etaDelta P.eigenvalue.re δ) m0 Dp p.ε p.ν hεpos
  rw [hεeq] at hDres hRnn
  have hPres := hP' p.ν hνpos (le_trans hpν hNUP) Cs hCs r hr
  rw [← hT] at hPres
  have hDfin := hDres.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcD (pow_nonneg ht0 kD)) hRnn)
  have hRfin := hPres.trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcP (pow_nonneg ht0 kP)) he)
  have hDl := hDfin.trans (mul_le_mul_of_nonneg_left hRfin
    (mul_nonneg hcD0 (pow_nonneg ht0 kD)))
  have hQδ : cF * p.ν⁻¹ ^ kF * (cD * p.ν⁻¹ ^ kD * (cP * p.ν⁻¹ ^ kP * Real.exp (-T / (2 * p.ν))))
      < 1 / 2 := by
    have := hQ p.ν hνpos (le_trans hpν hNUQ)
    calc _ = cF * cD * cP * p.ν⁻¹ ^ (kF + kD + kP) * Real.exp (-T / (2 * p.ν)) := by ring
      _ < 1 / 2 := this
  -- the inverse comparison
  obtain ⟨DNinv, hDNl, hDNr, hNI1, hNI2⟩ :=
    nearInverseComparison (gainEquiv p.c mZ (UnforcedLeray.Short.IIb.rhoB p m0 C0 k0)
      P.eigenvalue.re p.ν_pos) o.D0 (Ring.inverse o.D0) o.DN _ _
      (Ring.inverse_mul_cancel o.D0 hUD0) (Ring.mul_inverse_cancel o.D0 hUD0) hQbd hDl hQδ
  have hUDN : IsUnit o.DN := isUnit_iff_exists.2 ⟨DNinv, hDNr, hDNl⟩
  have hinv : Ring.inverse o.DN = DNinv := by
    have hDNl' : DNinv * o.DN = 1 := hDNl
    calc Ring.inverse o.DN = (DNinv * o.DN) * Ring.inverse o.DN := by rw [hDNl', one_mul]
      _ = DNinv * (o.DN * Ring.inverse o.DN) := mul_assoc _ _ _
      _ = DNinv := by rw [Ring.mul_inverse_cancel o.DN hUDN, mul_one]
  refine ⟨hUD0, hUDN, ?_, ?_, hSN⟩
  · rw [hinv]
    refine hNI1.trans ?_
    have hpow : p.ν⁻¹ ^ kF ≤ p.ν⁻¹ ^ kT := pow_le_pow_right₀ ht1 (by omega)
    calc 2 * (cF * p.ν⁻¹ ^ kF) = (2 * cF) * p.ν⁻¹ ^ kF := by ring
      _ ≤ CC * p.ν⁻¹ ^ kT := mul_le_mul hCC2 hpow (pow_nonneg ht0 _) hCC0
  · rw [hinv]
    refine hNI2.trans ?_
    have hpow : p.ν⁻¹ ^ (2 * kF + kD + kP) ≤ p.ν⁻¹ ^ kT := pow_le_pow_right₀ ht1 (by omega)
    calc 2 * (cF * p.ν⁻¹ ^ kF) ^ 2 * (cD * p.ν⁻¹ ^ kD * (cP * p.ν⁻¹ ^ kP * Real.exp (-T / (2 * p.ν))))
        = (2 * (cF ^ 2 * cD * cP)) * p.ν⁻¹ ^ (2 * kF + kD + kP) * Real.exp (-T / (2 * p.ν)) := by
          ring
      _ ≤ (2 * (cF ^ 2 * cD * cP)) * p.ν⁻¹ ^ kT * Real.exp (-T / (2 * p.ν)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) he
      _ ≤ CC * p.ν⁻¹ ^ kT * Real.exp (-T / (2 * p.ν)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC3 (pow_nonneg ht0 _)) he

end UnforcedLeray.Short.PartIIIb.NearInst
